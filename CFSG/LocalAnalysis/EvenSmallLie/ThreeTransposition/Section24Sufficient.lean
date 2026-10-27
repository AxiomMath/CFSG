module

public import CFSG.LocalAnalysis.EvenSmallLie.ThreeTransposition.Section24Connected
public import CFSG.LocalAnalysis.ZStar
public import CFSG.GroupTheory.HyperplaneGeneration

public section

namespace CFSG.EvenSmallLie.ThreeTransposition

open CFSG.Blueprint.Fischer CFSG.Fischer
open scoped Pointwise

variable {G : Type} [Group G]

section Class

variable {D : Set G}

theorem conj_mem_of_class (hclass : ∃ d₀ : G, D = {g | IsConj d₀ g}) :
    ∀ g : G, ∀ x ∈ D, g * x * g⁻¹ ∈ D :=
  fun g _ hx => Timmesfeld.conj_mem_of_isClass hclass g hx

theorem exists_conj_of_class (hclass : ∃ d₀ : G, D = {g | IsConj d₀ g}) {x y : G} (hx : x ∈ D)
    (hy : y ∈ D) : ∃ g : G, g * x * g⁻¹ = y :=
  isConj_iff.1 (Timmesfeld.isConj_of_isClass hclass hx hy)

theorem conj_mem_localClass (hDinv : ∀ g : G, ∀ x ∈ D, g * x * g⁻¹ ∈ D) (g : G) {c x : G}
    (hx : x ∈ LocalClass D c) : g * x * g⁻¹ ∈ LocalClass D (g * c * g⁻¹) :=
  ⟨hDinv g x hx.1, fun h => hx.2.1 (conj_injective h), (conj_commute_iff g x c).2 hx.2.2⟩

theorem orderOf_mul_mem_of_localClass (hclass : ∃ d₀ : G, D = {g | IsConj d₀ g}) {d : G}
    (hd : d ∈ D)
    (horder : ∀ x ∈ LocalClass D d, ∀ y ∈ LocalClass D d, orderOf (x * y) ∈ ({1, 2, 3} : Set ℕ))
    {c : G} (hc : c ∈ D) {x y : G} (hx : x ∈ LocalClass D c) (hy : y ∈ LocalClass D c) :
    orderOf (x * y) ∈ ({1, 2, 3} : Set ℕ) := by
  obtain ⟨g, hg⟩ := exists_conj_of_class hclass hc hd
  have hx' := conj_mem_localClass (conj_mem_of_class hclass) g hx
  have hy' := conj_mem_localClass (conj_mem_of_class hclass) g hy
  rw [hg] at hx' hy'
  have h := horder _ hx' _ hy'
  have e := orderOf_injective (MulAut.conj g).toMonoidHom (MulAut.conj g).injective (x * y)
  simp only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply] at e
  rwa [conj_mul_conj, e] at h

end Class

section OneFourOne

variable {D : Set G}

theorem exists_commute_of_path (hclass : ∃ d₀ : G, D = {g | IsConj d₀ g}) {d : G} (hd : d ∈ D)
    (hii : ∀ b ∈ LocalClass D d, ∀ a ∈ D, a * d ≠ d * a → a ∈ LocalClass D b →
      ∀ c ∈ LocalClass D d, ∃ f ∈ LocalClass D a ∩ LocalClass D d, f * c = c * f)
    {c p b a : G} (hc : c ∈ D) (hp : p ∈ D) (hb : b ∈ D) (ha : a ∈ D) (hcp : c * p = p * c)
    (hpb : p * b = b * p) (hba : b * a = a * b) : ∃ f ∈ D, f * c = c * f ∧ f * a = a * f := by
  have hDinv := conj_mem_of_class hclass
  by_cases hca : c * a = a * c
  · exact ⟨c, hc, rfl, hca⟩
  by_cases hpa : p * a = a * p
  · exact ⟨p, hp, hcp.symm, hpa⟩
  by_cases hcb : c * b = b * c
  · exact ⟨b, hb, hcb.symm, hba⟩
  obtain ⟨g, hg⟩ := exists_conj_of_class hclass hp hd
  have hbp : b ≠ p := fun h => hcb (by rw [h]; exact hcp)
  have hab : a ≠ b := fun h => hpa (by rw [h]; exact hpb)
  have hcp' : c ≠ p := fun h => hcb (by rw [h]; exact hpb)
  have hb' : g * b * g⁻¹ ∈ LocalClass D d := by
    rw [← hg]
    exact conj_mem_localClass hDinv g ⟨hb, hbp, hpb.symm⟩
  have ha' : g * a * g⁻¹ ∈ LocalClass D (g * b * g⁻¹) :=
    conj_mem_localClass hDinv g ⟨ha, hab, hba.symm⟩
  have hc' : g * c * g⁻¹ ∈ LocalClass D d := by
    rw [← hg]
    exact conj_mem_localClass hDinv g ⟨hc, hcp', hcp⟩
  have hfar : g * a * g⁻¹ * d ≠ d * (g * a * g⁻¹) := by
    rw [← hg, Ne, conj_commute_iff]
    exact fun h => hpa h.symm
  obtain ⟨f, ⟨hfa, -⟩, hfc⟩ := hii _ hb' _ (hDinv g a ha) hfar ha' _ hc'
  refine ⟨g⁻¹ * f * g, by simpa using hDinv g⁻¹ f hfa.1, ?_, ?_⟩
  · have h := (conj_commute_iff g⁻¹ f (g * c * g⁻¹)).2 hfc
    rwa [show g⁻¹ * (g * c * g⁻¹) * g⁻¹⁻¹ = c by group, inv_inv] at h
  · have h := (conj_commute_iff g⁻¹ f (g * a * g⁻¹)).2 hfa.2.2
    rwa [show g⁻¹ * (g * a * g⁻¹) * g⁻¹⁻¹ = a by group, inv_inv] at h

theorem exists_commute_of_reachable (hclass : ∃ d₀ : G, D = {g | IsConj d₀ g}) {d : G}
    (hd : d ∈ D)
    (hii : ∀ b ∈ LocalClass D d, ∀ a ∈ D, a * d ≠ d * a → a ∈ LocalClass D b →
      ∀ c ∈ LocalClass D d, ∃ f ∈ LocalClass D a ∩ LocalClass D d, f * c = c * f)
    {u w : D} (h : (commGraph D).Reachable u w) :
    ∃ p ∈ D, p * u = u * p ∧ p * w = w * p := by
  rw [SimpleGraph.reachable_iff_reflTransGen] at h
  induction h using Relation.ReflTransGen.head_induction_on with
  | refl => exact ⟨w, w.2, rfl, rfl⟩
  | head hab _ ih =>
    obtain ⟨p, hp, hpb, hpw⟩ := ih
    rw [commGraph_adj_iff] at hab
    exact exists_commute_of_path hclass hd hii (Subtype.prop _) (Subtype.prop _) hp
      (Subtype.prop _) hab.2 hpb.symm hpw

theorem component_isThreeTranspositionSet_of_orders (hclass : ∃ d₀ : G, D = {g | IsConj d₀ g})
    (hD2 : ∀ x ∈ D, orderOf x = 2) {d : G} (hd : d ∈ D)
    (horder : ∀ x ∈ LocalClass D d, ∀ y ∈ LocalClass D d, orderOf (x * y) ∈ ({1, 2, 3} : Set ℕ))
    (hii : ∀ b ∈ LocalClass D d, ∀ a ∈ D, a * d ≠ d * a → a ∈ LocalClass D b →
      ∀ c ∈ LocalClass D d, ∃ f ∈ LocalClass D a ∩ LocalClass D d, f * c = c * f) :
    IsThreeTranspositionSet (Subtype.val '' ((commGraph D).connectedComponentMk ⟨d, hd⟩).supp) := by
  have hDinv := conj_mem_of_class hclass
  rw [image_supp_connectedComponentMk hd]
  refine ⟨fun x hx => hD2 x (compSet_subset d hx), fun g hg x hx => ?_, fun u hu w hw => ?_⟩
  · have hle : Subgroup.closure (compSet D d) ≤ Subgroup.normalizer (compSet D d) := by
      rw [Subgroup.closure_le]
      intro u hu
      rw [SetLike.mem_coe, ← compSet_eq hu, mem_normalizer_compSet_iff hDinv
        (compSet_subset d hu), show u * u * u⁻¹ = u by group]
      exact mem_compSet_self (compSet_subset d hu)
    exact (Subgroup.mem_set_normalizer_iff.1 (hle hg) x).1 hx
  · obtain ⟨_, huD, hu'⟩ := hu
    obtain ⟨_, hwD, hw'⟩ := hw
    obtain ⟨p, hp, hpu, hpw⟩ := exists_commute_of_reachable hclass hd hii (hu'.symm.trans hw')
    have hu2 := mul_self_of_orderOf (hD2 u huD)
    have hw2 := mul_self_of_orderOf (hD2 w hwD)
    by_cases huw : u * w = w * u
    · rcases (commute_iff_orderOf_mul hu2 hw2).1 huw with h | h <;> simp [h]
    · have hup : u ≠ p := fun h => huw (by rw [h]; exact hpw)
      have hwp : w ≠ p := fun h => huw (by rw [h]; exact hpu.symm)
      exact orderOf_mul_mem_of_localClass hclass hd horder hp ⟨huD, hup, hpu.symm⟩
        ⟨hwD, hwp, hpw.symm⟩

theorem orderOf_mul_mem_of_pair {d : G}
    (hi : Pair (LocalGroup D d) {x | (x : G) ∈ LocalClass D d}) {x y : G}
    (hx : x ∈ LocalClass D d) (hy : y ∈ LocalClass D d) :
    orderOf (x * y) ∈ ({1, 2, 3} : Set ℕ) := by
  have h := hi.2.2.2.1 ⟨x, Subgroup.subset_closure hx⟩ hx ⟨y, Subgroup.subset_closure hy⟩ hy
  rwa [← Subgroup.orderOf_coe] at h

end OneFourOne

section Transport

variable {D : Set G}

theorem forall_sylow_of_conj [Finite G] (hDinv : ∀ g : G, ∀ x ∈ D, g * x * g⁻¹ ∈ D)
    (Φ : Set G → Prop) (hΦ : ∀ (g : G) (Ω : Set G), Φ Ω → Φ ((fun x => g * x * g⁻¹) '' Ω))
    {T : Sylow 2 G} (hT : Φ ((T : Set G) ∩ D)) (S : Sylow 2 G) : Φ ((S : Set G) ∩ D) := by
  obtain ⟨g, rfl⟩ := MulAction.exists_smul_eq G T S
  rw [smul_sylow_inter_eq_image hDinv T g]
  exact hΦ g _ hT

theorem pairwise_commute_image (g : G) {Ω : Set G} (h : ∀ x ∈ Ω, ∀ y ∈ Ω, x * y = y * x) :
    ∀ x ∈ (fun x => g * x * g⁻¹) '' Ω, ∀ y ∈ (fun x => g * x * g⁻¹) '' Ω, x * y = y * x := by
  rintro _ ⟨x, hx, rfl⟩ _ ⟨y, hy, rfl⟩
  exact (conj_commute_iff g x y).2 (h x hx y hy)

theorem subset_closure_products_image (g : G) {Ω : Set G}
    (h : Ω ⊆ Subgroup.closure {x | ∃ a ∈ Ω, ∃ b ∈ Ω, a * b = x}) :
    (fun x => g * x * g⁻¹) '' Ω ⊆ Subgroup.closure {x | ∃ a ∈ (fun x => g * x * g⁻¹) '' Ω,
      ∃ b ∈ (fun x => g * x * g⁻¹) '' Ω, a * b = x} := by
  rintro _ ⟨x, hx, rfl⟩
  have hmap := Subgroup.mem_map_of_mem (MulAut.conj g).toMonoidHom (h hx)
  rw [MonoidHom.map_closure] at hmap
  refine Subgroup.closure_mono ?_ hmap
  rintro _ ⟨_, ⟨a, ha, b, hb, rfl⟩, rfl⟩
  exact ⟨g * a * g⁻¹, ⟨a, ha, rfl⟩, g * b * g⁻¹, ⟨b, hb, rfl⟩, by simp [mul_assoc]⟩

theorem injective_products_image (g : G) {Ω : Set G}
    (h : ∀ a ∈ Ω, ∀ b ∈ Ω, ∀ a' ∈ Ω, ∀ b' ∈ Ω, a ≠ b → a' ≠ b' → a * b = a' * b' →
      (a = a' ∧ b = b') ∨ (a = b' ∧ b = a')) :
    ∀ a ∈ (fun x => g * x * g⁻¹) '' Ω, ∀ b ∈ (fun x => g * x * g⁻¹) '' Ω,
      ∀ a' ∈ (fun x => g * x * g⁻¹) '' Ω, ∀ b' ∈ (fun x => g * x * g⁻¹) '' Ω,
        a ≠ b → a' ≠ b' → a * b = a' * b' → (a = a' ∧ b = b') ∨ (a = b' ∧ b = a') := by
  rintro _ ⟨a, ha, rfl⟩ _ ⟨b, hb, rfl⟩ _ ⟨a', ha', rfl⟩ _ ⟨b', hb', rfl⟩ hab hab' heq
  beta_reduce at hab hab' heq ⊢
  rw [conj_mul_conj, conj_mul_conj] at heq
  rcases h a ha b hb a' ha' b' hb' (fun e => hab (by rw [e])) (fun e => hab' (by rw [e]))
    (conj_injective heq) with ⟨h1, h2⟩ | ⟨h1, h2⟩
  · exact Or.inl ⟨by rw [h1], by rw [h2]⟩
  · exact Or.inr ⟨by rw [h1], by rw [h2]⟩

end Transport

section Groups

theorem conj_eq_of_centralizes_odd {Q : Type} [Group Q] {N : Subgroup Q}
    (hN : Odd (Nat.card N)) {t : Q} (ht2 : t * t = 1) (htN : ∀ g : Q, g * t * g⁻¹ * t⁻¹ ∈ N)
    (hcent : ∀ n ∈ N, n * t = t * n) (g : Q) : g * t * g⁻¹ = t := by
  have hu := htN g
  set u := g * t * g⁻¹ * t⁻¹ with hu_def
  have hut := hcent u hu
  have hgt : g * t * g⁻¹ = u * t := by
    rw [hu_def]
    group
  have h1 : u * t * (u * t) = 1 := by
    rw [← hgt, show g * t * g⁻¹ * (g * t * g⁻¹) = g * (t * t) * g⁻¹ by group, ht2, mul_one,
      mul_inv_cancel]
  have hsq : u * u = 1 := by
    calc u * u = u * u * (t * t) := by rw [ht2, mul_one]
      _ = u * t * (u * t) := by
        rw [mul_assoc u t, ← mul_assoc t u t, ← hut]
        simp only [mul_assoc]
      _ = 1 := h1
  have h2 : orderOf u ∣ 2 := orderOf_dvd_of_pow_eq_one (by rw [pow_two]; exact hsq)
  have hN' : orderOf u ∣ Nat.card N := by
    have h := orderOf_dvd_natCard (⟨u, hu⟩ : N)
    rwa [← Subgroup.orderOf_coe] at h
  have h1' : orderOf u = 1 := by
    rcases (Nat.dvd_prime Nat.prime_two).1 h2 with h | h
    · exact h
    · rw [h] at hN'
      exact absurd hN' fun h => Nat.not_even_iff_odd.2 hN (even_iff_two_dvd.2 h)
  rw [hgt, orderOf_eq_one_iff.1 h1', one_mul]

theorem commute_of_hyperplanes {Q A : Type} [Group Q] [Finite Q] [Group A] [Finite A]
    [IsElementaryAbelian 2 A] [Nontrivial A] {N : Subgroup Q} [N.Normal] (hN : Odd (Nat.card N))
    (ψ : A →* Q) (t : Q)
    (hB : ∀ B : Subgroup A, B.index = 2 → ∃ b ∈ B, ∀ n ∈ N, n * ψ b = ψ b * n → n * t = t * n) :
    ∀ n ∈ N, n * t = t * n := by
  let _ : MulDistribMulAction A N :=
    MulDistribMulAction.compHom N ((MulAut.conjNormal (H := N)).comp ψ)
  have hsmul : ∀ (b : A) (n : N), ((b • n : N) : Q) = ψ b * n * (ψ b)⁻¹ :=
    fun b n => MulAut.conjNormal_apply (ψ b) n
  have hgen := SolvableHall.coprime_hyperplane_generation (p := 2) (A := A) (H := N)
    (fun h => Nat.not_even_iff_odd.2 hN (even_iff_two_dvd.2 h))
  have hle : ⨆ (B : Subgroup A) (_ : B.index = 2), fixedPointSubgroup B N ≤
      (Subgroup.centralizer {t}).comap N.subtype := by
    refine iSup₂_le fun B hB2 => ?_
    obtain ⟨b, hbB, hb⟩ := hB B hB2
    intro n hn
    have h : ψ b * n * (ψ b)⁻¹ = n := by
      have h0 := congrArg Subtype.val (hn ⟨b, hbB⟩)
      rwa [Subgroup.smul_def, hsmul] at h0
    rw [Subgroup.mem_comap, Subgroup.coe_subtype, Subgroup.mem_centralizer_singleton_iff]
    exact hb n n.2 (mul_eq_of_conj_eq h).symm
  intro n hn
  have hmem : (⟨n, hn⟩ : N) ∈ ⨆ (B : Subgroup A) (_ : B.index = 2), fixedPointSubgroup B N := by
    rw [hgen]
    exact Subgroup.mem_top _
  exact Subgroup.mem_centralizer_singleton_iff.1 (hle hmem)

theorem mul_mul_self_eq_of_mul_eq {d e y : G} (hd : d * d = 1) (he : e * e = 1)
    (hdy : d * y = y * d) (h : d * e = e * d * y) : e * d * (e * d) = y := by
  calc e * d * (e * d) = e * (d * e) * d := by simp only [mul_assoc]
    _ = e * (e * d * y) * d := by rw [h]
    _ = e * e * (d * (y * d)) := by simp only [mul_assoc]
    _ = d * (d * y) := by rw [he, one_mul, ← hdy]
    _ = y := by rw [← mul_assoc, hd, one_mul]

end Groups

section OneFourTwo

variable [Finite G] {D : Set G}

theorem conj_eq_or_conj_eq_of_sq (hDinv : ∀ g : G, ∀ x ∈ D, g * x * g⁻¹ ∈ D)
    (hD2 : ∀ x ∈ D, orderOf x = 2)
    (hPC : ∀ S : Sylow 2 G, ∀ x ∈ (S : Set G) ∩ D, ∀ y ∈ (S : Set G) ∩ D, x * y = y * x)
    (hINJ : ∀ S : Sylow 2 G, ∀ a ∈ (S : Set G) ∩ D, ∀ b ∈ (S : Set G) ∩ D,
      ∀ a' ∈ (S : Set G) ∩ D, ∀ b' ∈ (S : Set G) ∩ D,
        a ≠ b → a' ≠ b' → a * b = a' * b' → (a = a' ∧ b = b') ∨ (a = b' ∧ b = a'))
    {a d : G} (ha : a ∈ D) (hd : d ∈ D) (had : a ≠ d) (hc : a * d = d * a) {h : G}
    (hh : h * (a * d) = a * d * h)
    (hsq : h * d * h⁻¹ * d * (h * d * h⁻¹ * d) = 1 ∨
      h * d * h⁻¹ * d * (h * d * h⁻¹ * d) = a * d) :
    h * d * h⁻¹ = d ∨ h * d * h⁻¹ = a := by
  have ha2 := mul_self_of_orderOf (hD2 a ha)
  have hd2 := mul_self_of_orderOf (hD2 d hd)
  have hd'D : h * d * h⁻¹ ∈ D := hDinv h d hd
  have hd'2 : h * d * h⁻¹ * (h * d * h⁻¹) = 1 := mul_self_of_orderOf (hD2 _ hd'D)
  have hy2 : a * d * (a * d) = 1 := mul_mul_self_of_commute ha2 hd2 hc
  have hdy : d * (a * d) = a * d * d := by rw [← mul_assoc, ← hc]
  have hhc : Commute h (a * d) := hh
  have hd'y : Commute (h * d * h⁻¹) (a * d) :=
    (hhc.mul_left (hdy : Commute d (a * d))).mul_left hhc.inv_left
  rcases hsq with hsq | hsq
  ·
    have hd'd : h * d * h⁻¹ * d = d * (h * d * h⁻¹) :=
      (Timmesfeld.commute_iff_mul_sq_eq_one hd'2 hd2).2 (by rw [pow_two]; exact hsq)
    have hd'a : h * d * h⁻¹ * a = a * (h * d * h⁻¹) := by
      have h3 : Commute (h * d * h⁻¹) (a * d * d) := hd'y.mul_right hd'd
      rwa [mul_assoc a d d, hd2, mul_one] at h3
    have hS : ∀ x ∈ ({a, d, h * d * h⁻¹} : Set G), ∀ y ∈ ({a, d, h * d * h⁻¹} : Set G),
        x * y = y * x := by
      rintro x (rfl | rfl | rfl) y (rfl | rfl | rfl) <;>
        first | rfl | assumption | exact Eq.symm ‹_›
    have hS2 : ∀ x ∈ ({a, d, h * d * h⁻¹} : Set G), x * x = 1 := by
      rintro x (rfl | rfl | rfl)
      exacts [ha2, hd2, hd'2]
    obtain ⟨S, hSS⟩ := exists_sylow_of_pairwise hS hS2
    have haS : a ∈ (S : Set G) ∩ D := ⟨hSS (by simp), ha⟩
    have hdS : d ∈ (S : Set G) ∩ D := ⟨hSS (by simp), hd⟩
    have hd'S : h * d * h⁻¹ ∈ (S : Set G) ∩ D := ⟨hSS (by simp), hd'D⟩
    have hyS : ∀ u ∈ (S : Set G) ∩ D, u * (a * d) = a * d * u := fun u hu =>
      Commute.mul_right (hPC S u hu a haS : Commute u a) (hPC S u hu d hdS)
    obtain ⟨k, ⟨hkN, hky⟩, hkd⟩ :=
      exists_mem_normalizer_conj_eq hDinv S (hPC S) hyS hdS hd'S hh rfl
    have hka : k * a * k⁻¹ ∈ (S : Set G) ∩ D := (Subgroup.mem_set_normalizer_iff.1 hkN a).1 haS
    have hprod : k * a * k⁻¹ * (h * d * h⁻¹) = a * d := by
      rw [← hkd, conj_mul_conj, Subgroup.mem_centralizer_singleton_iff.1 hky,
        mul_inv_cancel_right]
    have hne : k * a * k⁻¹ ≠ h * d * h⁻¹ := by
      rw [← hkd]
      exact fun e => had (conj_injective e)
    rcases hINJ S _ hka _ hd'S a haS d hdS hne had hprod with ⟨-, h2⟩ | ⟨-, h2⟩
    · exact Or.inl h2
    · exact Or.inr h2
  ·
    exfalso
    have h4 : (h * d * h⁻¹ * d) ^ 2 ^ 2 = 1 := by
      rw [show 2 ^ 2 = 2 * 2 by norm_num, pow_mul, pow_two (h * d * h⁻¹ * d), hsq, pow_two, hy2]
    obtain ⟨S, hSS⟩ := (Timmesfeld.isPGroup_two_closure_pair hd'2 hd2 h4).exists_le_sylow
    have hcm := hPC S _ ⟨hSS (Subgroup.subset_closure (by simp)), hd'D⟩ d
      ⟨hSS (Subgroup.subset_closure (by simp)), hd⟩
    have h1 : a * d = 1 := by
      rw [← hsq]
      exact mul_mul_self_of_commute hd'2 hd2 hcm
    exact had (by rw [eq_inv_of_mul_eq_one_left h1, inv_of_orderOf (hD2 d hd)])

theorem commute_of_commute_mul_of_sufficient (hDinv : ∀ g : G, ∀ x ∈ D, g * x * g⁻¹ ∈ D)
    (hD2 : ∀ x ∈ D, orderOf x = 2)
    (horder : ∀ c ∈ D, ∀ x ∈ LocalClass D c, ∀ y ∈ LocalClass D c,
      orderOf (x * y) ∈ ({1, 2, 3} : Set ℕ))
    (hPC : ∀ S : Sylow 2 G, ∀ x ∈ (S : Set G) ∩ D, ∀ y ∈ (S : Set G) ∩ D, x * y = y * x)
    (hGEN : ∀ S : Sylow 2 G, (S : Set G) ∩ D ⊆
      Subgroup.closure {x | ∃ a ∈ (S : Set G) ∩ D, ∃ b ∈ (S : Set G) ∩ D, a * b = x})
    (hINJ : ∀ S : Sylow 2 G, ∀ a ∈ (S : Set G) ∩ D, ∀ b ∈ (S : Set G) ∩ D,
      ∀ a' ∈ (S : Set G) ∩ D, ∀ b' ∈ (S : Set G) ∩ D,
        a ≠ b → a' ≠ b' → a * b = a' * b' → (a = a' ∧ b = b') ∨ (a = b' ∧ b = a'))
    {a d : G} (ha : a ∈ D) (hd : d ∈ D) (had : a ≠ d) (hc : a * d = d * a) {e : G}
    (he : e ∈ D) (hey : e * (a * d) = a * d * e) : e * d = d * e := by
  have ha2 := mul_self_of_orderOf (hD2 a ha)
  have hd2 := mul_self_of_orderOf (hD2 d hd)
  have hd1 : d ≠ 1 := ne_one_of_orderOf (hD2 d hd)
  have hy2 : a * d * (a * d) = 1 := mul_mul_self_of_commute ha2 hd2 hc
  have hdy : d * (a * d) = a * d * d := by rw [← mul_assoc, ← hc]
  have hdad : d * (a * d) = a := by rw [← mul_assoc, ← hc, mul_assoc, hd2, mul_one]
  set H : Subgroup G := Subgroup.centralizer {a * d} with hH_def
  have hmemH : ∀ x : G, x ∈ H ↔ x * (a * d) = a * d * x := fun x => by
    rw [hH_def]
    exact Subgroup.mem_centralizer_singleton_iff
  have hyH : a * d ∈ H := (hmemH _).2 rfl
  have hdH : d ∈ H := (hmemH d).2 hdy
  set Y : Subgroup H := Subgroup.zpowers ⟨a * d, hyH⟩ with hY_def
  have hY : ∀ z : H, z ∈ Y ↔ (z : G) = 1 ∨ (z : G) = a * d := by
    intro z
    have hy2' : (⟨a * d, hyH⟩ : H) * ⟨a * d, hyH⟩ = 1 := Subtype.ext hy2
    rw [hY_def, mem_zpowers_iff_of_mul_self hy2']
    exact or_congr Subtype.ext_iff Subtype.ext_iff
  have hYc : Y ≤ Subgroup.center H := by
    rw [hY_def, Subgroup.zpowers_le, Subgroup.mem_center_iff]
    exact fun z => Subtype.ext ((hmemH z).1 z.2)
  have : Y.Normal := Subgroup.normal_of_le_center hYc
  have hmk : ∀ x z : H, (QuotientGroup.mk x : H ⧸ Y) = QuotientGroup.mk z ↔
      (z : G) = x ∨ (z : G) = x * (a * d) := by
    intro x z
    rw [QuotientGroup.eq, hY]
    simp only [Subgroup.coe_mul, Subgroup.coe_inv]
    constructor
    · rintro (h | h)
      · exact Or.inl (inv_mul_eq_one.1 h).symm
      · exact Or.inr (inv_mul_eq_iff_eq_mul.1 h)
    · rintro (h | h)
      · exact Or.inl (by rw [h, inv_mul_cancel])
      · exact Or.inr (by rw [h, inv_mul_cancel_left])
  set t : H ⧸ Y := QuotientGroup.mk ⟨d, hdH⟩ with ht_def
  have hwc : ∀ x : H, (x : G) * d * (x : G)⁻¹ * d * ((x : G) * d * (x : G)⁻¹ * d) = 1 ∨
      (x : G) * d * (x : G)⁻¹ * d * ((x : G) * d * (x : G)⁻¹ * d) = a * d →
      (QuotientGroup.mk (x * ⟨d, hdH⟩ * x⁻¹) : H ⧸ Y) = t := by
    intro x hsq
    rw [ht_def]
    refine (hmk _ _).2 ?_
    simp only [Subgroup.coe_mul, Subgroup.coe_inv]
    rcases conj_eq_or_conj_eq_of_sq hDinv hD2 hPC hINJ ha hd had hc ((hmemH x).1 x.2) hsq with
      h | h
    · exact Or.inl (by rw [h])
    · exact Or.inr (by rw [h, ← mul_assoc, ha2, one_mul])
  have ht1 : t ≠ 1 := by
    intro h
    rw [ht_def] at h
    rcases (hmk ⟨d, hdH⟩ 1).1 (h.trans (QuotientGroup.mk_one Y).symm) with h' | h'
    · exact hd1 h'.symm
    · exact ne_one_of_orderOf (hD2 a ha) (hdad.symm.trans h'.symm)
  have ht2 : t * t = 1 := by
    rw [ht_def, ← QuotientGroup.mk_mul, show (⟨d, hdH⟩ : H) * ⟨d, hdH⟩ = 1 from Subtype.ext hd2,
      QuotientGroup.mk_one]
  have hiso : ∀ g : H ⧸ Y, g * t * g⁻¹ * t = t * (g * t * g⁻¹) → g * t * g⁻¹ = t := by
    intro g hg
    obtain ⟨x, rfl⟩ := QuotientGroup.mk_surjective g
    have hconj : (QuotientGroup.mk x : H ⧸ Y) * t * (QuotientGroup.mk x)⁻¹ =
        QuotientGroup.mk (x * ⟨d, hdH⟩ * x⁻¹) := by
      rw [ht_def, QuotientGroup.mk_mul, QuotientGroup.mk_mul, QuotientGroup.mk_inv]
    rw [hconj] at hg ⊢
    refine hwc x ?_
    rw [ht_def, ← QuotientGroup.mk_mul, ← QuotientGroup.mk_mul] at hg
    rcases (hmk _ _).1 hg with h | h <;>
      simp only [Subgroup.coe_mul, Subgroup.coe_inv] at h
    · exact Or.inl (mul_mul_self_of_commute (mul_self_of_orderOf (hD2 _ (hDinv x d hd))) hd2
        h.symm)
    · exact Or.inr (mul_mul_self_eq_of_mul_eq hd2 (mul_self_of_orderOf (hD2 _ (hDinv x d hd)))
        hdy h)
  let _ : Fintype (H ⧸ Y) := Fintype.ofFinite _
  obtain ⟨N, hNn, hNodd, hNt⟩ := CFSG.ZStar.glauberman_zStar (H ⧸ Y) t ht1 ht2 hiso
  have : N.Normal := hNn
  have hpad : ∀ x ∈ ({a, d} : Set G), ∀ y ∈ ({a, d} : Set G), x * y = y * x := by
    rintro x (rfl | rfl) y (rfl | rfl) <;> first | rfl | assumption | exact Eq.symm ‹_›
  obtain ⟨S, hSS⟩ := exists_sylow_of_pairwise hpad (by rintro x (rfl | rfl); exacts [ha2, hd2])
  have haS : a ∈ (S : Set G) ∩ D := ⟨hSS (by simp), ha⟩
  have hdS : d ∈ (S : Set G) ∩ D := ⟨hSS (by simp), hd⟩
  have hΩy : ∀ u ∈ (S : Set G) ∩ D, u * (a * d) = a * d * u := fun u hu =>
    Commute.mul_right (hPC S u hu a haS : Commute u a) (hPC S u hu d hdS)
  set A : Subgroup G := Subgroup.closure ((S : Set G) ∩ D) with hA_def
  have hAH : A ≤ H := by
    rw [hA_def]
    exact (Subgroup.closure_le _).2 fun u hu => (hmemH u).2 (hΩy u hu)
  let ψ : A →* H ⧸ Y := (QuotientGroup.mk' Y).comp (Subgroup.inclusion hAH)
  have : IsElementaryAbelian 2 A :=
    { toIsMulCommutative := Subgroup.isMulCommutative_closure fun x hx y hy _ => hPC S x hx y hy
      exponent_dvd_p := Monoid.exponent_dvd_of_forall_pow_eq_one fun g => Subtype.ext (by
        rw [Subgroup.coe_pow, Subgroup.coe_one, pow_two]
        exact mul_self_of_mem_closure_of_pairwise (hPC S)
          (fun x hx => mul_self_of_orderOf (hD2 x hx.2)) g.2) }
  have : Nontrivial A :=
    ⟨⟨⟨d, Subgroup.subset_closure hdS⟩, 1, fun h => hd1 (congrArg Subtype.val h)⟩⟩
  have hB : ∀ B : Subgroup A, B.index = 2 →
      ∃ b ∈ B, ∀ n ∈ N, n * ψ b = ψ b * n → n * t = t * n := by
    intro B hB2
    obtain ⟨b, hbΩ, hbB⟩ : ∃ b, ∃ hb : b ∈ (S : Set G) ∩ D,
        (⟨b, Subgroup.subset_closure hb⟩ : A) ∈ B := by
      by_contra hne
      push Not at hne
      have hprod : {x | ∃ e ∈ (S : Set G) ∩ D, ∃ f ∈ (S : Set G) ∩ D, e * f = x} ⊆
          (B.map A.subtype : Set G) := by
        rintro _ ⟨e, he, f, hf, rfl⟩
        refine ⟨⟨e, Subgroup.subset_closure he⟩ * ⟨f, Subgroup.subset_closure hf⟩, ?_, rfl⟩
        rw [SetLike.mem_coe, Subgroup.mul_mem_iff_of_index_two hB2]
        exact iff_of_false (hne e he) (hne f hf)
      obtain ⟨z, hzB, hz⟩ := (Subgroup.closure_le _).2 hprod (hGEN S hdS)
      have hz' : z = ⟨d, Subgroup.subset_closure hdS⟩ := Subtype.ext hz
      exact hne d hdS (hz' ▸ hzB)
    refine ⟨⟨b, Subgroup.subset_closure hbΩ⟩, hbB, fun n _ hn => ?_⟩
    obtain ⟨x, rfl⟩ := QuotientGroup.mk_surjective n
    have hψb : ψ ⟨b, Subgroup.subset_closure hbΩ⟩ = QuotientGroup.mk ⟨b, hAH
        (Subgroup.subset_closure hbΩ)⟩ := rfl
    rw [hψb, ← QuotientGroup.mk_mul, ← QuotientGroup.mk_mul] at hn
    have hxb := (hmk _ _).1 hn
    simp only [Subgroup.coe_mul] at hxb
    have hx : (x : G) * (a * d) = a * d * x := (hmemH x).1 x.2
    have hbd : b * d = d * b := hPC S b hbΩ d hdS
    have hd'D : (x : G) * d * (x : G)⁻¹ ∈ D := hDinv x d hd
    have hd'2 := mul_self_of_orderOf (hD2 _ hd'D)
    have hxc : Commute (x : G) (a * d) := hx
    have hd'y : Commute ((x : G) * d * (x : G)⁻¹) (a * d) :=
      (hxc.mul_left (hdy : Commute d (a * d))).mul_left hxc.inv_left
    have hxb' : (x : G) * b * (x : G)⁻¹ = b ∨ (x : G) * b * (x : G)⁻¹ = b * (a * d) := by
      rcases hxb with h | h
      · exact Or.inl (by rw [← h, mul_inv_cancel_right])
      · refine Or.inr ?_
        have h' : (x : G) * b = b * x * (a * d) := by
          calc (x : G) * b = x * b * (a * d * (a * d)) := by rw [hy2, mul_one]
            _ = b * x * (a * d) := by rw [← mul_assoc, ← h]
        calc (x : G) * b * (x : G)⁻¹ = b * x * (a * d) * (x : G)⁻¹ := by rw [h']
          _ = b * ((x : G) * (a * d) * (x : G)⁻¹) := by simp only [mul_assoc]
          _ = b * (a * d) := by rw [hx, mul_inv_cancel_right]
    have hd'b : (x : G) * d * (x : G)⁻¹ * b = b * ((x : G) * d * (x : G)⁻¹) := by
      have hcb := (conj_commute_iff (x : G) d b).2 hbd.symm
      rcases hxb' with h | h
      · rwa [h] at hcb
      · rw [h] at hcb
        have h3 : Commute ((x : G) * d * (x : G)⁻¹) (b * (a * d) * (a * d)) :=
          Commute.mul_right (hcb : Commute _ (b * (a * d))) hd'y
        rwa [mul_assoc b, hy2, mul_one] at h3
    have hd'd : (x : G) * d * (x : G)⁻¹ * d = d * ((x : G) * d * (x : G)⁻¹) := by
      by_cases hbd' : b = d
      · rwa [hbd'] at hd'b
      by_cases hba : b = a
      · rw [hba] at hd'b
        have h3 : Commute ((x : G) * d * (x : G)⁻¹) (a * (a * d)) :=
          Commute.mul_right (hd'b : Commute _ a) hd'y
        rwa [← mul_assoc, ha2, one_mul] at h3
      by_cases hd'b' : (x : G) * d * (x : G)⁻¹ = b
      · rw [hd'b']
        exact hbd
      have hE := isOddTranspositionSet_of_orders (horder b hbΩ.2)
      have hdE : d ∈ LocalClass D b := ⟨hd, fun h => hbd' h.symm, (hPC S d hdS b hbΩ)⟩
      have haE : a ∈ LocalClass D b := ⟨ha, fun h => hba h.symm, (hPC S a haS b hbΩ)⟩
      exact hE.commute_of_commute_mul (fun y hy => hD2 y hy.1) hdE ⟨haE, had, hc⟩
        ⟨hd'D, hd'b', hd'b⟩ (by rw [← hc]; exact hd'y)
    have hq := hwc x (Or.inl (mul_mul_self_of_commute hd'2 hd2 hd'd))
    refine mul_eq_of_conj_eq ?_
    calc (QuotientGroup.mk x : H ⧸ Y) * t * (QuotientGroup.mk x)⁻¹ =
        QuotientGroup.mk (x * ⟨d, hdH⟩ * x⁻¹) := by
          rw [ht_def, QuotientGroup.mk_mul, QuotientGroup.mk_mul, QuotientGroup.mk_inv]
      _ = t := hq
  have hcentN := commute_of_hyperplanes hNodd ψ t hB
  have hcent := conj_eq_of_centralizes_odd hNodd ht2 hNt hcentN
  have heH : e ∈ H := (hmemH e).2 hey
  have h5 := hcent (QuotientGroup.mk ⟨e, heH⟩)
  rw [ht_def, ← QuotientGroup.mk_inv, ← QuotientGroup.mk_mul, ← QuotientGroup.mk_mul] at h5
  rcases (hmk _ _).1 h5 with h | h <;>
    simp only [Subgroup.coe_mul, Subgroup.coe_inv] at h
  · exact mul_eq_of_conj_eq h.symm
  ·
    have he2 := mul_self_of_orderOf (hD2 e he)
    have hede : e * d * e⁻¹ = a := by
      calc e * d * e⁻¹ = e * d * e⁻¹ * (a * d * (a * d)) := by rw [hy2, mul_one]
        _ = d * (a * d) := by rw [← mul_assoc, ← h]
        _ = a := hdad
    have hsq : e * d * (e * d) = a * d := by
      calc e * d * (e * d) = e * d * e⁻¹ * d := by
            rw [inv_of_orderOf (hD2 e he)]
            simp only [mul_assoc]
        _ = a * d := by rw [hede]
    have h4 : (e * d) ^ 2 ^ 2 = 1 := by
      rw [show 2 ^ 2 = 2 * 2 by norm_num, pow_mul, pow_two (e * d), hsq, pow_two, hy2]
    obtain ⟨S', hS'⟩ := (Timmesfeld.isPGroup_two_closure_pair he2 hd2 h4).exists_le_sylow
    exact hPC S' e ⟨hS' (Subgroup.subset_closure (by simp)), he⟩ d
      ⟨hS' (Subgroup.subset_closure (by simp)), hd⟩

theorem connected_isThreeTranspositionSet_of_orders (hclass : ∃ d₀ : G, D = {g | IsConj d₀ g})
    (hD2 : ∀ x ∈ D, orderOf x = 2) {d : G} (hd : d ∈ D)
    (horder : ∀ x ∈ LocalClass D d, ∀ y ∈ LocalClass D d, orderOf (x * y) ∈ ({1, 2, 3} : Set ℕ))
    (hii : ∀ b ∈ LocalClass D d, ∀ a ∈ D, a * d ≠ d * a → a ∈ LocalClass D b →
      ∀ c ∈ LocalClass D d, ∃ f ∈ LocalClass D a ∩ LocalClass D d, f * c = c * f)
    (T : Sylow 2 G)
    (hiii : ∀ x ∈ Subgroup.closure ((T : Set G) ∩ D),
      ∀ y ∈ Subgroup.closure ((T : Set G) ∩ D), x * y = y * x)
    (hiv : Subgroup.closure ((T : Set G) ∩ D) =
      Subgroup.closure {x | ∃ a ∈ (T : Set G) ∩ D, ∃ b ∈ (T : Set G) ∩ D, a * b = x})
    (hv : ∀ a ∈ (T : Set G) ∩ D, ∀ b ∈ (T : Set G) ∩ D, ∀ a' ∈ (T : Set G) ∩ D,
      ∀ b' ∈ (T : Set G) ∩ D, a ≠ b → a' ≠ b' → a * b = a' * b' →
        (a = a' ∧ b = b') ∨ (a = b' ∧ b = a'))
    (h1 : {x | x ∈ Subgroup.closure ((T : Set G) ∩ D) ∧ x ≠ 1} ≠ (T : Set G) ∩ D)
    (h2 : ∀ a ∈ (T : Set G) ∩ D, ∀ b ∈ (T : Set G) ∩ D, ∀ c ∈ (T : Set G) ∩ D,
      ¬ ∀ e ∈ (T : Set G) ∩ D, ∀ f ∈ (T : Set G) ∩ D,
        ∃ g ∈ Subgroup.normalizer ((T : Set G) ∩ D) ⊓ Subgroup.centralizer {a * b * c},
          g * e * g⁻¹ = f)
    (h3 : ∀ Δ : (commGraph D).ConnectedComponent,
      ∀ x ∈ Subgroup.normalizer (Subtype.val '' Δ.supp), orderOf x = 2 →
        ∃ f ∈ Subtype.val '' Δ.supp, x * f * x⁻¹ = f) :
    (commGraph D).Connected ∧ IsThreeTranspositionSet D := by
  have hDinv := conj_mem_of_class hclass
  have horder' : ∀ c ∈ D, ∀ x ∈ LocalClass D c, ∀ y ∈ LocalClass D c,
      orderOf (x * y) ∈ ({1, 2, 3} : Set ℕ) :=
    fun c hc x hx y hy => orderOf_mul_mem_of_localClass hclass hd horder hc hx hy
  have hPC := forall_sylow_of_conj hDinv (fun Ω => ∀ x ∈ Ω, ∀ y ∈ Ω, x * y = y * x)
    (fun g _ h => pairwise_commute_image g h)
    (T := T) fun x hx y hy => hiii x (Subgroup.subset_closure hx) y (Subgroup.subset_closure hy)
  have hGEN := forall_sylow_of_conj hDinv
    (fun Ω => Ω ⊆ Subgroup.closure {x | ∃ a ∈ Ω, ∃ b ∈ Ω, a * b = x})
    (fun g _ h => subset_closure_products_image g h)
    (T := T) fun x hx => hiv ▸ Subgroup.subset_closure hx
  have hINJ := forall_sylow_of_conj hDinv
    (fun Ω => ∀ a ∈ Ω, ∀ b ∈ Ω, ∀ a' ∈ Ω, ∀ b' ∈ Ω, a ≠ b → a' ≠ b' → a * b = a' * b' →
      (a = a' ∧ b = b') ∨ (a = b' ∧ b = a'))
    (fun g _ h => injective_products_image g h) (T := T) hv
  have hodd : IsOddTranspositionSet D := by
    refine (isOddTranspositionSet_iff hD2 fun g _ x hx => hDinv g x hx).2 fun a ha b hb => ?_
    ext c
    simp only [Set.mem_inter_iff, SetLike.mem_coe, Subgroup.mem_centralizer_singleton_iff]
    constructor
    · rintro ⟨hc, hcab⟩
      have hba : b * a = a * b := hb.2.2
      refine ⟨⟨hc, ?_⟩, hc, ?_⟩
      · exact commute_of_commute_mul_of_sufficient hDinv hD2 horder' hPC hGEN hINJ hb.1 ha hb.2.1
          hba hc (by rw [hba]; exact hcab)
      · exact commute_of_commute_mul_of_sufficient hDinv hD2 horder' hPC hGEN hINJ ha hb.1
          (fun h => hb.2.1 h.symm) hba.symm hc hcab
    · rintro ⟨⟨hc, hca⟩, -, hcb⟩
      exact ⟨hc, by rw [← mul_assoc, hca, mul_assoc, hcb, ← mul_assoc]⟩
  have hconn := hodd.connected_of_sylow hDinv hD2 T h1 h2 h3
  refine ⟨hconn, ?_⟩
  have hcomp := component_isThreeTranspositionSet_of_orders hclass hD2 hd horder hii
  rw [image_supp_connectedComponentMk hd] at hcomp
  have hall : compSet D d = D := Set.Subset.antisymm (compSet_subset d) fun x hx =>
    ⟨hd, hx, hconn.preconnected _ _⟩
  rwa [hall] at hcomp

theorem connected_isThreeTranspositionSet (hclass : ∃ d₀ : G, D = {g | IsConj d₀ g})
    (hD2 : ∀ x ∈ D, orderOf x = 2) {d : G} (hd : d ∈ D)
    (hi : Pair (LocalGroup D d) {x | (x : G) ∈ LocalClass D d} ∧ 1 < (LocalClass D d).ncard)
    (hii : ∀ b ∈ LocalClass D d, ∀ a ∈ D, a * d ≠ d * a → a ∈ LocalClass D b →
      ∀ c ∈ LocalClass D d, ∃ f ∈ LocalClass D a ∩ LocalClass D d, f * c = c * f)
    (T : Sylow 2 G)
    (hiii : ∀ x ∈ Subgroup.closure ((T : Set G) ∩ D),
      ∀ y ∈ Subgroup.closure ((T : Set G) ∩ D), x * y = y * x)
    (hiv : Subgroup.closure ((T : Set G) ∩ D) =
      Subgroup.closure {x | ∃ a ∈ (T : Set G) ∩ D, ∃ b ∈ (T : Set G) ∩ D, a * b = x})
    (hv : ∀ a ∈ (T : Set G) ∩ D, ∀ b ∈ (T : Set G) ∩ D, ∀ a' ∈ (T : Set G) ∩ D,
      ∀ b' ∈ (T : Set G) ∩ D, a ≠ b → a' ≠ b' → a * b = a' * b' →
        (a = a' ∧ b = b') ∨ (a = b' ∧ b = a'))
    (h1 : {x | x ∈ Subgroup.closure ((T : Set G) ∩ D) ∧ x ≠ 1} ≠ (T : Set G) ∩ D)
    (h2 : ∀ a ∈ (T : Set G) ∩ D, ∀ b ∈ (T : Set G) ∩ D, ∀ c ∈ (T : Set G) ∩ D,
      ¬ ∀ e ∈ (T : Set G) ∩ D, ∀ f ∈ (T : Set G) ∩ D,
        ∃ g ∈ Subgroup.normalizer ((T : Set G) ∩ D) ⊓ Subgroup.centralizer {a * b * c},
          g * e * g⁻¹ = f)
    (h3 : ∀ Δ : (commGraph D).ConnectedComponent,
      ∀ x ∈ Subgroup.normalizer (Subtype.val '' Δ.supp), orderOf x = 2 →
        ∃ f ∈ Subtype.val '' Δ.supp, x * f * x⁻¹ = f) :
    (commGraph D).Connected ∧ IsThreeTranspositionSet D :=
  connected_isThreeTranspositionSet_of_orders hclass hD2 hd
    (fun _ hx _ hy => orderOf_mul_mem_of_pair hi.1 hx hy) hii T hiii hiv hv h1 h2 h3

end OneFourTwo

end CFSG.EvenSmallLie.ThreeTransposition
