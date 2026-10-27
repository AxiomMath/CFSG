module

public import CFSG.Holt.H78.Sec4Prop43B3
import CFSG.Holt.H78.Sec4Box
import CFSG.Holt.H78.Sec4CCLMatch

public section

namespace CFSG.Holt.H78

open MulAction CFSG.Holt CFSG.Open
open scoped Pointwise

theorem fusionIsSylowIn_subgroupOf {K : Type*} [Group K] {p : ℕ} {S H B : Subgroup K}
    (hS : fusionIsSylowIn p S H) (hHB : H ≤ B) :
    fusionIsSylowIn p (S.subgroupOf B) (H.subgroupOf B) := by
  refine ⟨fun x hx => hS.1 hx, hS.2.1.comap_of_injective B.subtype B.subtype_injective,
    fun Q hQH hQ hSQ => ?_⟩
  have h1 : Q.map B.subtype ≤ H := by
    rintro _ ⟨q, hq, rfl⟩
    exact hQH hq
  have h2 : S ≤ Q.map B.subtype := fun x hx => ⟨⟨x, hHB (hS.1 hx)⟩, hSQ hx, rfl⟩
  have h3 := hS.2.2 _ h1 (hQ.map B.subtype) h2
  ext x
  constructor
  · intro hx
    have : (x : K) ∈ Q.map B.subtype := ⟨x, hx, rfl⟩
    rw [h3] at this
    exact this
  · intro hx
    exact hSQ hx

theorem card_map_le_card {K L : Type*} [Group K] [Group L] [Finite K] (f : K →* L)
    (A : Subgroup K) : Nat.card (A.map f) ≤ Nat.card A :=
  Nat.card_le_card_of_surjective (fun a : A => (⟨f a, a, a.2, rfl⟩ : A.map f))
    (fun ⟨_, a, ha, rfl⟩ => ⟨⟨a, ha⟩, rfl⟩)

theorem eq_one_of_mem_of_odd {K : Type*} [Group K] [Finite K] {A B : Subgroup K}
    (hA : IsPGroup 2 A) (hB : Odd (Nat.card B)) {g : K} (hgA : g ∈ A) (hgB : g ∈ B) : g = 1 := by
  obtain ⟨k, hk⟩ := hA ⟨g, hgA⟩
  have hk' : g ^ 2 ^ k = 1 := congrArg Subtype.val hk
  obtain ⟨m, -, hm⟩ := (Nat.dvd_prime_pow Nat.prime_two).mp (orderOf_dvd_of_pow_eq_one hk')
  have h1 : orderOf g ∣ Nat.card B := Subgroup.orderOf_dvd_natCard B hgB
  rw [hm] at h1
  rcases m with _ | m
  · rw [pow_zero, orderOf_eq_one_iff] at hm
    exact hm
  · have h2 := Nat.dvd_trans (dvd_pow_self 2 (Nat.succ_ne_zero m)) h1
    have h3 := Nat.odd_iff.mp hB
    omega

namespace HoltData

variable {K X : Type*} [Group K] [MulAction K X] (D : HoltData K X)

theorem eq_one_of_matched {α β : X} {ι' : Type*} [DecidableEq ι'] {Λc : ι' → Type*}
    [∀ j, Fintype (Λc j)] (e : holtDelta K X α β ≃ ∀ j, Λc j) {k : D.ι} {j : ι'}
    (hcard : Fintype.card (D.Ψc k) = Fintype.card (Λc j) + 2)
    (hab : D.coord α k ≠ D.coord β k)
    (hδ : ∀ δ δ' : holtDelta K X α β, (D.coord (δ : X) k = D.coord (δ' : X) k ↔ e δ j = e δ' j) ∧
      D.coord (δ : X) k ≠ D.coord α k ∧ D.coord (δ : X) k ≠ D.coord β k)
    (δ₀ : holtDelta K X α β) {π : Equiv.Perm (D.Ψc k)} (hπa : π (D.coord α k) = D.coord α k)
    (hπb : π (D.coord β k) = D.coord β k)
    (hπδ : ∀ δ : holtDelta K X α β, π (D.coord (δ : X) k) = D.coord (δ : X) k) : π = 1 := by
  classical
  set g : Λc j → D.Ψc k := fun l => D.coord ((e.symm (Function.update (e δ₀) j l) : _) : X) k
    with hgdef
  have hg : Function.Injective g := by
    intro l l' h
    have h1 := ((hδ (e.symm (Function.update (e δ₀) j l))
      (e.symm (Function.update (e δ₀) j l'))).1).mp h
    simpa using h1
  have hrange : ∀ δ : holtDelta K X α β, D.coord (δ : X) k ∈ Set.range g := by
    intro δ
    refine ⟨e δ j, ?_⟩
    refine ((hδ _ δ).1).mpr ?_
    simp
  have hbg : D.coord β k ∉ Set.range g := by
    rintro ⟨l, hl⟩
    exact (hδ (e.symm (Function.update (e δ₀) j l)) δ₀).2.2 hl
  have hag : D.coord α k ∉ insert (D.coord β k) (Set.range g) := by
    rintro (h | ⟨l, hl⟩)
    · exact hab h
    · exact (hδ (e.symm (Function.update (e δ₀) j l)) δ₀).2.1 hl
  have huniv : insert (D.coord α k) (insert (D.coord β k) (Set.range g)) = Set.univ := by
    refine Set.eq_of_subset_of_ncard_le (Set.subset_univ _) ?_ (Set.toFinite _)
    rw [Set.ncard_insert_of_notMem hag (Set.toFinite _),
      Set.ncard_insert_of_notMem hbg (Set.toFinite _), Set.ncard_range_of_injective hg,
      Set.ncard_univ, Nat.card_eq_fintype_card, Nat.card_eq_fintype_card, hcard]
  refine Equiv.ext fun p => ?_
  have hp : p ∈ insert (D.coord α k) (insert (D.coord β k) (Set.range g)) := by
    rw [huniv]
    exact Set.mem_univ p
  rcases hp with rfl | rfl | ⟨l, rfl⟩
  · exact hπa
  · exact hπb
  · exact hπδ _

theorem exists_isPGroup_of_parallel [Finite K] {v y : jHull K X} (hvS : (v : K) ∈ D.socPre)
    (hv2 : v * v = 1) {k : D.ι} (hyL : (y : K) ∈ D.L k) (hy2 : D.ρ k y * D.ρ k y = 1)
    (hy1 : D.ρ k y ≠ 1) (hv1 : D.ρ k v ≠ 1) (hyv : D.ρ k y ≠ D.ρ k v)
    (hcomm : D.ρ k v * D.ρ k y = D.ρ k y * D.ρ k v) :
    ∃ E : Subgroup K, IsPGroup 2 E ∧ (v : K) ∈ E ∧ 4 ≤ Nat.card E ∧
      ∀ e ∈ E, ∃ h : e ∈ jHull K X, e ∈ D.socPre ∧ e * e = 1 ∧
        ∀ j, D.ρ j ⟨e, h⟩ = 1 ∨ D.ρ j ⟨e, h⟩ = D.ρ j v ∨ D.ρ j ⟨e, h⟩ = D.ρ j y ∨
          D.ρ j ⟨e, h⟩ = D.ρ j v * D.ρ j y := by
  classical
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  set Y : Subgroup K := jOddCore K X ⊔ Subgroup.zpowers (v : K) ⊔ Subgroup.zpowers (y : K)
    with hYdef
  have hYH : Y ≤ jHull K X := sup_le (sup_le jOddCore_le_jHull
    ((Subgroup.zpowers_le).mpr v.2)) ((Subgroup.zpowers_le).mpr y.2)
  have hYS : Y ≤ D.socPre := sup_le (sup_le D.jOddCore_le_socPre
    ((Subgroup.zpowers_le).mpr hvS)) ((Subgroup.zpowers_le).mpr (D.L_le_socPre k hyL))
  have hρ : ∀ j, ∀ e (he : e ∈ Y), D.ρ j ⟨e, hYH he⟩ ∈ Subgroup.closure {D.ρ j v, D.ρ j y} := by
    intro j
    set T : Subgroup K := ((Subgroup.closure {D.ρ j v, D.ρ j y}).comap (D.ρ j)).map
      (jHull K X).subtype
    have hYT : Y ≤ T := by
      refine sup_le (sup_le (fun o ho => ⟨⟨o, jOddCore_le_jHull ho⟩, ?_, rfl⟩)
        ((Subgroup.zpowers_le).mpr ⟨v, Subgroup.subset_closure (by simp), rfl⟩))
        ((Subgroup.zpowers_le).mpr ⟨y, Subgroup.subset_closure (by simp), rfl⟩)
      change D.ρ j ⟨o, jOddCore_le_jHull ho⟩ ∈ Subgroup.closure {D.ρ j v, D.ρ j y}
      rw [D.rho_eq_one_of_mem_jOddCore (h := ⟨o, jOddCore_le_jHull ho⟩) ho]
      exact one_mem _
    intro e he
    obtain ⟨e', he', rfl⟩ := hYT he
    exact he'
  have hpair : ∀ j, D.ρ j v * D.ρ j v = 1 ∧ D.ρ j y * D.ρ j y = 1 ∧
      D.ρ j v * D.ρ j y = D.ρ j y * D.ρ j v := by
    intro j
    by_cases hjk : j = k
    · subst hjk
      exact ⟨by rw [← map_mul, hv2, map_one], hy2, hcomm⟩
    · have : D.ρ j y = 1 := D.rho_eq_one_of_mem_L (Ne.symm hjk) hyL
      rw [this]
      exact ⟨by rw [← map_mul, hv2, map_one], one_mul 1, by rw [mul_one, one_mul]⟩
  have hsq : ∀ j, ∀ π ∈ Subgroup.closure {D.ρ j v, D.ρ j y}, π * π = 1 := by
    intro j π hπ
    obtain ⟨ha, hb, hab⟩ := hpair j
    rcases mem_closure_pair_of_commute ha hb hab hπ with rfl | rfl | rfl | rfl
    · exact one_mul 1
    · exact ha
    · exact hb
    · calc D.ρ j v * D.ρ j y * (D.ρ j v * D.ρ j y)
          = D.ρ j v * D.ρ j v * (D.ρ j y * D.ρ j y) := by
            rw [mul_assoc, ← mul_assoc (D.ρ j y), ← hab, mul_assoc, mul_assoc]
        _ = 1 := by rw [ha, hb, one_mul]
  have hv2' : (v : K) * v = 1 := congrArg Subtype.val hv2
  have hvp : IsPGroup 2 (Subgroup.zpowers (v : K)) := by
    have hvo : orderOf (v : K) ∣ 2 ^ 1 :=
      orderOf_dvd_of_pow_eq_one (by rw [pow_one, sq]; exact hv2')
    obtain ⟨m, -, hm⟩ := (Nat.dvd_prime_pow Nat.prime_two).mp hvo
    exact IsPGroup.of_card (by rw [Nat.card_zpowers, hm])
  have hvY : (v : K) ∈ Y :=
    (le_sup_right.trans le_sup_left : Subgroup.zpowers (v : K) ≤ Y) (Subgroup.mem_zpowers _)
  have hyY : (y : K) ∈ Y := (le_sup_right : Subgroup.zpowers (y : K) ≤ Y) (Subgroup.mem_zpowers _)
  obtain ⟨E, hvE, hE⟩ := exists_fusionIsSylowIn_ge hvp ((Subgroup.zpowers_le).mpr hvY)
  refine ⟨E, hE.2.1, hvE (Subgroup.mem_zpowers _), ?_, fun e he => ?_⟩
  ·
    set E' := E.subgroupOf (jHull K X)
    set Y' := Y.subgroupOf (jHull K X)
    have hE' : fusionIsSylowIn 2 E' Y' := fusionIsSylowIn_subgroupOf hE hYH
    have hmap := fusionIsSylowIn_map (D.ρ k) hE'
    have hY'2 : IsPGroup 2 (Y'.map (D.ρ k)) := by
      rintro ⟨π, ⟨e, he, rfl⟩⟩
      refine ⟨1, Subtype.ext ?_⟩
      change D.ρ k e ^ 2 = 1
      rw [sq]
      exact hsq k _ (hρ k e he)
    have heq : E'.map (D.ρ k) = Y'.map (D.ρ k) := (hmap.2.2 _ le_rfl hY'2 hmap.1).symm
    have hmem : ∀ e (he : e ∈ Y), D.ρ k ⟨e, hYH he⟩ ∈ Y'.map (D.ρ k) := fun e he =>
      ⟨⟨e, hYH he⟩, he, rfl⟩
    have hsub : ({1, D.ρ k v, D.ρ k y, D.ρ k v * D.ρ k y} : Set (Equiv.Perm (D.Ψc k))) ⊆
        (Y'.map (D.ρ k) : Set (Equiv.Perm (D.Ψc k))) := by
      intro π hπ
      rcases hπ with rfl | rfl | rfl | rfl
      · exact one_mem _
      · exact hmem _ hvY
      · exact hmem _ hyY
      · rw [← map_mul]
        exact hmem _ (Y.mul_mem hvY hyY)
    have hvv : D.ρ k v * D.ρ k v = 1 := (hpair k).1
    have h4set : ({1, D.ρ k v, D.ρ k y, D.ρ k v * D.ρ k y} :
        Set (Equiv.Perm (D.Ψc k))).ncard = 4 := by
      have hn1 : D.ρ k v * D.ρ k y ≠ 1 := fun h => hyv (by
        rw [← one_mul (D.ρ k y), ← hvv, mul_assoc, h, mul_one])
      have hn2 : D.ρ k v * D.ρ k y ≠ D.ρ k v := fun h =>
        hy1 (mul_left_cancel (a := D.ρ k v) (by rw [h, mul_one]))
      have hn3 : D.ρ k v * D.ρ k y ≠ D.ρ k y := fun h =>
        hv1 (mul_right_cancel (b := D.ρ k y) (by rw [h, one_mul]))
      rw [Set.ncard_insert_of_notMem (by
          simp only [Set.mem_insert_iff, Set.mem_singleton_iff, not_or]
          exact ⟨hv1.symm, hy1.symm, hn1.symm⟩),
        Set.ncard_insert_of_notMem (by
          simp only [Set.mem_insert_iff, Set.mem_singleton_iff, not_or]
          exact ⟨hyv.symm, hn2.symm⟩),
        Set.ncard_pair hn3.symm]
    calc 4 = ({1, D.ρ k v, D.ρ k y, D.ρ k v * D.ρ k y} :
          Set (Equiv.Perm (D.Ψc k))).ncard := h4set.symm
      _ ≤ (Y'.map (D.ρ k) : Set (Equiv.Perm (D.Ψc k))).ncard :=
          Set.ncard_le_ncard hsub (Set.toFinite _)
      _ = Nat.card (Y'.map (D.ρ k)) := (Nat.card_coe_set_eq _).symm
      _ = Nat.card (E'.map (D.ρ k)) := by rw [heq]
      _ ≤ Nat.card E' := card_map_le_card _ _
      _ = Nat.card E := Nat.card_congr (Subgroup.subgroupOfEquivOfLe (hE.1.trans hYH)).toEquiv
  · have heY := hE.1 he
    refine ⟨hYH heY, hYS heY, ?_, fun j => mem_closure_pair_of_commute (hpair j).1 (hpair j).2.1
      (hpair j).2.2 (hρ j e heY)⟩
    have h1 : ∀ j, D.ρ j ⟨e * e, hYH (Y.mul_mem heY heY)⟩ = 1 := fun j => by
      have : (⟨e * e, hYH (Y.mul_mem heY heY)⟩ : jHull K X) = ⟨e, hYH heY⟩ * ⟨e, hYH heY⟩ := rfl
      rw [this, map_mul]
      exact hsq j _ (hρ j e heY)
    have hker := (D.mem_jOrbitKernel_iff_rho (h := ⟨e * e, hYH (Y.mul_mem heY heY)⟩)).mpr h1
    have hO : e * e ∈ jOddCore K X := by
      rw [← D.socPre_inf_jOrbitKernel]
      exact ⟨hYS (Y.mul_mem heY heY), hker⟩
    exact eq_one_of_mem_of_odd hE.2.1 odd_card_jOddCore (E.mul_mem he he) hO

end HoltData

namespace AltConfig

variable {G : Type} [Group G] [Finite G] {Ω : Type} [Fintype Ω] [DecidableEq Ω] [MulAction G Ω]
  [FaithfulSMul G Ω] {α β : Ω} (C : AltConfig G Ω α β)

theorem smul_eq_of_lemma44 (hS : Sec4Setting G Ω) (hαβ : α ≠ β)
    (hT : Odd (Nat.card (twoPointKernel G Ω α β))) (hP : fusionIsSylowIn 2 C.calP C.calG)
    {i : C.D.ι} (h4 : Fintype.card (C.D.Ψc i) % 4 = 1)
    {R : Subgroup G} (hRQ : R ≤ C.calP ⊓ C.kerC i) {s r : C.kerC i} (hsP : (s : G) ∈ C.calP)
    (hsR : (s : G) ∉ R) (hrR : (r : G) ∈ R)
    (hQ : ∀ q ∈ C.calP ⊓ C.kerC i, q ∈ R ∨ (s : G) * q ∈ R)
    (hs2 : C.kerCHom i s * C.kerCHom i s = 1) (hr2 : C.kerCHom i r * C.kerCHom i r = 1)
    (hsr : C.kerCHom i s * C.kerCHom i r = C.kerCHom i r * C.kerCHom i s)
    (hsfree : ∀ c, c ≠ C.D.coord C.γ i → C.kerCHom i s c ≠ c)
    (hrfree : ∀ c, c ≠ C.D.coord C.γ i → C.kerCHom i r c ≠ c)
    (hsrfree : ∀ c, c ≠ C.D.coord C.γ i → C.kerCHom i (s * r) c ≠ c) :
    ∀ ω ∈ fixSet Ω R, (s : G) • ω = ω := by
  classical
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hrP : (r : G) ∈ C.calP := (Subgroup.mem_inf.mp (hRQ hrR)).1
  have hsQ : (s : G) ∈ C.calP ⊓ C.kerC i := Subgroup.mem_inf.mpr ⟨hsP, s.2⟩
  have hss : (s : G) * s = 1 := C.eq_one_of_kerCHom_eq_one hT (q := s * s)
    (C.calP.mul_mem hsP hsP) (by rw [map_mul, hs2])
  have hsinv : (s : G)⁻¹ = s := inv_eq_of_mul_eq_one_right hss
  have hsN : ∀ g ∈ R, (s : G) * g * (s : G)⁻¹ ∈ R := by
    intro g hg
    have hmem : (s : G) * g * (s : G)⁻¹ ∈ C.calP ⊓ C.kerC i :=
      (C.calP ⊓ C.kerC i).mul_mem ((C.calP ⊓ C.kerC i).mul_mem hsQ (hRQ hg))
        ((C.calP ⊓ C.kerC i).inv_mem hsQ)
    rcases hQ _ hmem with h | h
    · exact h
    · exfalso
      apply hsR
      have h1 : (s : G) * ((s : G) * g * (s : G)⁻¹) = g * (s : G)⁻¹ := by
        rw [← mul_assoc, ← mul_assoc, hss, one_mul]
      rw [h1] at h
      have h2 : (s : G)⁻¹ ∈ R := by simpa using R.mul_mem (R.inv_mem hg) h
      rwa [hsinv] at h2
  have hsNorm : (s : G) ∈ Subgroup.normalizer (R : Set G) := by
    refine Subgroup.mem_normalizer_iff.mpr fun g => ⟨fun hg => hsN g hg, fun hg => ?_⟩
    have := hsN _ hg
    rwa [hsinv, ← mul_assoc, ← mul_assoc, hss, one_mul, mul_assoc, hss, mul_one] at this
  have hQN : ∀ q ∈ C.calP ⊓ C.kerC i, q ∈ Subgroup.normalizer (R : Set G) := by
    intro q hq
    rcases hQ q hq with h | h
    · exact Subgroup.le_normalizer h
    · have : q = (s : G) * ((s : G) * q) := by rw [← mul_assoc, hss, one_mul]
      rw [this]
      exact Subgroup.mul_mem _ hsNorm (Subgroup.le_normalizer h)
  obtain ⟨x, hx2, hxα, hxS, hxQ, y, hyJ, hyγ, hxy⟩ := C.exists_x_of_lemma44 hS hαβ hT hP h4
  have hxr := C.mul_mem_longInv_of_lemma44 hS hαβ hT hx2 hxα hxS hxQ hyJ hyγ hxy hrP hr2 hrfree
  have hsr2 : C.kerCHom i (s * r) * C.kerCHom i (s * r) = 1 := by
    rw [map_mul, mul_assoc, ← mul_assoc (C.kerCHom i r), ← hsr, mul_assoc, hr2, mul_one, hs2]
  have hxsr := C.mul_mem_longInv_of_lemma44 hS hαβ hT hx2 hxα hxS hxQ hyJ hyγ hxy (q := s * r)
    (C.calP.mul_mem hsP hrP) hsr2 hsrfree
  have hxC : x ∈ Subgroup.centralizer (R : Set G) :=
    Subgroup.mem_centralizer_iff.mpr fun g hg => (hxQ g (hRQ hg)).symm
  have hxN : x ∈ Subgroup.normalizer (R : Set G) := Subgroup.centralizer_le_normalizer _ hxC
  intro ω₀ hω₀
  by_contra hω₀s
  have hR : IsPGroup 2 R :=
    C.sylow.2.1.to_le (hRQ.trans (inf_le_left.trans inf_le_left))
  have hRαβ : R ≤ stabilizer G α ⊓ stabilizer G β :=
    hRQ.trans (inf_le_right.trans (C.kerC_le_inf i))
  have hr1 : (r : G) ≠ 1 := by
    intro h1
    have := C.nontrivial_Ψc i
    obtain ⟨c, hc⟩ := exists_ne (C.D.coord C.γ i)
    apply hrfree c hc
    rw [(Subtype.ext h1 : r = 1), map_one, Equiv.Perm.one_apply]
  have hR1 : R ≠ ⊥ := fun h => hr1 (by rw [h] at hrR; exact Subgroup.mem_bot.mp hrR)
  set a : fixSet Ω R := ⟨α, mem_fixSet_iff_le_stabilizer.mpr (hRαβ.trans inf_le_left)⟩ with ha
  set b : fixSet Ω R := ⟨β, mem_fixSet_iff_le_stabilizer.mpr (hRαβ.trans inf_le_right)⟩ with hb
  have hab : a ≠ b := fun h => hαβ (congrArg Subtype.val h)
  have h3 := hS.three_le_card_fixSet_of_ne hR hab
  have hRH : ∀ δ : holtDelta G Ω α β, (δ : Ω) ∈ fixSet Ω R ↔
      C.D.coord δ i = C.D.coord C.γ i := by
    intro δ
    refine ⟨fun hδ => ?_, fun hδ g hg => C.smul_eq_of_mem_kerC (Subgroup.mem_inf.mp (hRQ hg)).2 hδ⟩
    by_contra hne
    apply hrfree _ hne
    rw [← C.coord_smul_eq_kerCHom r (δ := δ) (δ' := δ) (hδ r hrR).symm]
  set Λc : ∀ j, Set (C.D.Ψc j) := Function.update (fun _ => Set.univ) i {C.D.coord C.γ i}
    with hΛc
  have hΛi : Λc i = {C.D.coord C.γ i} := Function.update_self _ _ _
  have hΛj : ∀ j, j ≠ i → Λc j = Set.univ := fun j hj => Function.update_of_ne hj _ _
  have hbox : ∀ δ : holtDelta G Ω α β, (δ : Ω) ∈ fixSet Ω R ↔ ∀ j, C.D.coord δ j ∈ Λc j := by
    intro δ
    rw [hRH δ]
    constructor
    · intro h j
      by_cases hj : j = i
      · subst hj
        rw [hΛi]
        exact h
      · rw [hΛj j hj]
        exact Set.mem_univ _
    · intro h
      have := h i
      rw [hΛi] at this
      exact this
  obtain ⟨e, he, hcoord, hreal⟩ := hS.exists_boxEquiv_ccl hαβ C.D C.oddCore_eq_bot C.alt hR
    (a := a) (b := b) rfl rfl Λc hbox (p := fun j => (Λc j).Nontrivial) (fun _ h => h)
    (fun _ h => Set.not_nontrivial_iff.mp h)
  obtain ⟨DK⟩ := hS.holtData_centralizerImage hR hR1 h3
  have h5 : ∀ j : {j // (Λc j).Nontrivial}, 5 ≤ Fintype.card (Λc j) := fun j => by
    have hji : (j : C.D.ι) ≠ i := fun h => by
      have := j.2
      rw [h, hΛi] at this
      exact Set.not_nontrivial_singleton this
    rw [← Nat.card_eq_fintype_card, Nat.card_coe_set_eq, hΛj _ hji, C.ncard_univ_Ψc]
    exact C.D.five_le_card _
  obtain ⟨cc, -, hcca, hccc, -⟩ := DK.ccl (hS.star_centralizerImage hR h3)
    (hS.holtTheorem1Below_centralizerImage hR hR1 h3) hab e h5 hcoord hreal
  have hRfixS : R ≤ fixingSubgroup G (fixSet Ω R) := fun g hg =>
    (mem_fixingSubgroup_iff G).mpr fun ω hω => hω g hg
  have hxrN : x * r ∈ Subgroup.normalizer (R : Set G) := mul_mem hxN (Subgroup.le_normalizer hrR)
  have hxsrN : x * ((s * r : C.kerC i) : G) ∈ Subgroup.normalizer (R : Set G) :=
    mul_mem hxN (mul_mem hsNorm (Subgroup.le_normalizer hrR))
  obtain ⟨c₁, hc₁J, hc₁C, hc₁⟩ := hS.frattini h3 hR hRfixS hxr
    (normalizer_le_stabilizer_fixSet R hxrN)
  obtain ⟨c₂, hc₂J, hc₂C, hc₂⟩ := hS.frattini h3 hR hRfixS hxsr
    (normalizer_le_stabilizer_fixSet R hxsrN)
  set u₁ : centralizerImage Ω R := centralizerImageElt (V := R) hc₁C
  set u₂ : centralizerImage Ω R := centralizerImageElt (V := R) hc₂C
  have hu₁ : u₁ ∈ longInv (centralizerImage Ω R) (fixSet Ω R) :=
    (hS.mem_longInv_centralizerImage_iff hR h3 u₁).mpr ⟨c₁, hc₁J, hc₁C, fun ω => rfl⟩
  have hu₂ : u₂ ∈ longInv (centralizerImage Ω R) (fixSet Ω R) :=
    (hS.mem_longInv_centralizerImage_iff hR h3 u₂).mpr ⟨c₂, hc₂J, hc₂C, fun ω => rfl⟩
  set sb : centralizerImage Ω R := u₁ * u₂ with hsbdef
  have hrfix : ∀ ω ∈ fixSet Ω R, (r : G) • ω = ω := fun ω hω => hω r hrR
  have hsb : ∀ ω : fixSet Ω R,
      ((sb : Equiv.Perm (fixSet Ω R)) ω : Ω) = (s : G) • (ω : Ω) := by
    intro ω
    have hsω : (s : G) • (ω : Ω) ∈ fixSet Ω R := smul_mem_fixSet_of_mem_normalizer hsNorm ω.2
    have hxsω : x • (s : G) • (ω : Ω) ∈ fixSet Ω R := smul_mem_fixSet_of_mem_normalizer hxN hsω
    change c₁ • c₂ • (ω : Ω) = (s : G) • (ω : Ω)
    rw [hc₂ ω ω.2, Subgroup.coe_mul, mul_smul, mul_smul, hrfix ω ω.2, hc₁ _ hxsω, mul_smul,
      hrfix _ hxsω, ← mul_smul, hx2, one_smul]
  have hsbS : sb ∈ DK.socPre := hS.mul_mem_socPre_centralizerImage hR h3 DK hu₁ hu₂
  have hsbH : sb ∈ jHull (centralizerImage Ω R) (fixSet Ω R) :=
    mul_mem (mem_jHull_of_mem_longInv hu₁) (mem_jHull_of_mem_longInv hu₂)
  set sh : jHull (centralizerImage Ω R) (fixSet Ω R) := ⟨sb, hsbH⟩ with hshdef
  have hsbsb : sb * sb = 1 := by
    apply Subtype.ext
    refine Equiv.ext fun ω => Subtype.ext ?_
    change ((sb : Equiv.Perm (fixSet Ω R)) ((sb : Equiv.Perm (fixSet Ω R)) ω) : Ω) = (ω : Ω)
    rw [hsb ((sb : Equiv.Perm (fixSet Ω R)) ω), hsb ω, ← mul_smul, hss, one_smul]
  have hsh2 : sh * sh = 1 := Subtype.ext hsbsb
  have hsb1 : sb ≠ 1 := by
    intro h
    apply hω₀s
    have := hsb ⟨ω₀, hω₀⟩
    rw [h] at this
    exact this.symm
  have hsα : (s : G) • α = α := mem_stabilizer_iff.mp (C.kerC_le_inf i s.2).1
  have hsβ : (s : G) • β = β := mem_stabilizer_iff.mp (C.kerC_le_inf i s.2).2
  have hmemΔ : ∀ δ : holtDelta (centralizerImage Ω R) (fixSet Ω R) a b,
      ((δ : fixSet Ω R) : Ω) ∈ holtDelta G Ω α β := fun δ =>
    (hS.mem_holtDelta_centralizerImage_iff hR h3 hab).mp δ.2
  have hsδ : ∀ δ : holtDelta (centralizerImage Ω R) (fixSet Ω R) a b,
      (s : G) • ((δ : fixSet Ω R) : Ω) = (δ : fixSet Ω R) := fun δ =>
    C.smul_eq_of_mem_kerC s.2 (δ := ⟨_, hmemΔ δ⟩) ((hRH ⟨_, hmemΔ δ⟩).mp (δ : fixSet Ω R).2)
  have hshfix : ∀ ω : fixSet Ω R, (s : G) • (ω : Ω) = ω →
      ((sh : centralizerImage Ω R) • ω) = ω := fun ω hω => Subtype.ext (by
    change ((sb : Equiv.Perm (fixSet Ω R)) ω : Ω) = ω
    rw [hsb, hω])
  have hρfix : ∀ ω : fixSet Ω R, (s : G) • (ω : Ω) = ω → ∀ k,
      DK.ρ k sh (DK.coord ω k) = DK.coord ω k := fun ω hω k => by
    rw [← DK.coord_smul, hshfix ω hω]
  obtain ⟨γK, hγK⟩ : ∃ γK : fixSet Ω R, (γK : Ω) = C.γ :=
    ⟨⟨C.γ, (hRH C.γ).mpr rfl⟩, rfl⟩
  have hγKΔ : γK ∈ holtDelta (centralizerImage Ω R) (fixSet Ω R) a b :=
    (hS.mem_holtDelta_centralizerImage_iff hR h3 hab).mpr (by rw [hγK]; exact C.γ.2)
  have hmatched : ∀ j', DK.ρ (cc j') sh = 1 := by
    intro j'
    obtain ⟨-, hcard, hab', hδ'⟩ := hcca j'
    exact DK.eq_one_of_matched e hcard hab' hδ' ⟨γK, hγKΔ⟩ (hρfix a hsα _) (hρfix b hsβ _)
      fun δ => hρfix _ (hsδ δ) _
  obtain ⟨k, hk⟩ : ∃ k, DK.ρ k sh ≠ 1 := by
    by_contra h
    push Not at h
    have hker : (sh : centralizerImage Ω R) ∈ jOrbitKernel (centralizerImage Ω R) (fixSet Ω R) :=
      (DK.mem_jOrbitKernel_iff_rho (h := sh)).mpr h
    have hO : sb ∈ jOddCore (centralizerImage Ω R) (fixSet Ω R) := by
      rw [← DK.socPre_inf_jOrbitKernel]
      exact ⟨hsbS, hker⟩
    have hsbp : IsPGroup 2 (Subgroup.zpowers sb) := by
      have hvo : orderOf sb ∣ 2 ^ 1 := orderOf_dvd_of_pow_eq_one (by rw [pow_one, sq]; exact hsbsb)
      obtain ⟨m, -, hm⟩ := (Nat.dvd_prime_pow Nat.prime_two).mp hvo
      exact IsPGroup.of_card (by rw [Nat.card_zpowers, hm])
    exact hsb1 (eq_one_of_mem_of_odd hsbp odd_card_jOddCore (Subgroup.mem_zpowers sb) hO)
  have hkpar : k ∉ Set.range cc := fun ⟨j', hj'⟩ => hk (hj' ▸ hmatched j')
  have hpar := hccc k hkpar
  have hmM : DK.ρ k sh ∈ DK.M k := DK.rho_mem_M_of_mem_socPre hsbS k
  have hm2 : DK.ρ k sh * DK.ρ k sh = 1 := by rw [← map_mul, hsh2, map_one]
  have hmc : DK.ρ k sh (DK.coord a k) = DK.coord a k := hρfix a hsα k
  obtain ⟨m', hm'M, hm'c, hm'2, hm'1, hm'm, hmm'⟩ :=
    (DK.factor k).exists_commute_involution hmM hm2 hk hmc
  obtain ⟨yy, hyyL, hyyρ⟩ := DK.mem_M.mp hm'M
  obtain ⟨E, hE2, hsbE, hE4, hEel⟩ := DK.exists_isPGroup_of_parallel (v := sh) (y := yy) hsbS
    hsh2 hyyL (by rw [hyyρ]; exact hm'2) (by rw [hyyρ]; exact hm'1) hk
    (by rw [hyyρ]; exact hm'm) (by rw [hyyρ]; exact hmm')
  have hEfix : ∀ e ∈ E, ∀ ω : fixSet Ω R, (s : G) • (ω : Ω) = ω →
      DK.coord ω k = DK.coord a k → e • ω = ω := by
    intro e he ω hsω hωk
    obtain ⟨heH, heS, he2, heρ⟩ := hEel e he
    have hyyfix : ∀ j, DK.ρ j yy (DK.coord ω j) = DK.coord ω j := by
      intro j
      by_cases hjk : j = k
      · subst hjk
        rw [hyyρ, hωk, hm'c]
      · rw [DK.rho_eq_one_of_mem_L (Ne.symm hjk) hyyL, Equiv.Perm.one_apply]
    have hcoordω : DK.coord ω = DK.coord (e • ω) := funext fun j => by
      have h1 := DK.coord_smul ⟨e, heH⟩ ω j
      change DK.coord ω j = DK.coord (e • ω) j
      rw [h1]
      rcases heρ j with h | h | h | h <;> rw [h]
      · rfl
      · exact (hρfix ω hsω j).symm
      · exact (hyyfix j).symm
      · rw [Equiv.Perm.mul_apply, hyyfix j, hρfix ω hsω j]
    have horb := (DK.coord_eq_iff ω (e • ω)).mp hcoordω
    by_cases he1 : e = 1
    · rw [he1, one_smul]
    · have ho : orderOf e = 2 := orderOf_eq_prime (by rw [sq]; exact he2) he1
      exact (hS.lemma_2_4_iv_centralizerImage hR hR1 h3 DK heH ho horb).1 heS ω
        (mem_orbit_self ω)
  set A := stabilizer G (fixSet Ω R) with hAdef
  set ψ : A →* Equiv.Perm (fixSet Ω R) := inducedHom A (fixSet Ω R) le_rfl with hψdef
  set Eperm : Subgroup (Equiv.Perm (fixSet Ω R)) := E.map (centralizerImage Ω R).subtype
    with hEpermdef
  have hQA : ∀ q ∈ C.calP ⊓ C.kerC i, q ∈ A := fun q hq =>
    normalizer_le_stabilizer_fixSet R (hQN q hq)
  set Q' : Subgroup A := (C.calP ⊓ C.kerC i).subgroupOf A with hQ'def
  set Et : Subgroup A := (C.kerC i).subgroupOf A ⊓ Eperm.comap ψ with hEtdef
  have hψR : ∀ g (hg : g ∈ A), g ∈ R → ψ ⟨g, hg⟩ = 1 := fun g hg hgR =>
    Equiv.ext fun ω => Subtype.ext (by rw [coe_inducedHom_apply]; exact ω.2 g hgR)
  have hψs : ψ ⟨s, hQA _ hsQ⟩ = (sb : Equiv.Perm (fixSet Ω R)) :=
    Equiv.ext fun ω => Subtype.ext (by rw [coe_inducedHom_apply, hsb])
  have hsbinv : (sb : Equiv.Perm (fixSet Ω R))⁻¹ = sb :=
    inv_eq_of_mul_eq_one_right (congrArg Subtype.val hsbsb)
  have hψQ : ∀ q (hq : q ∈ C.calP ⊓ C.kerC i),
      ψ ⟨q, hQA q hq⟩ = 1 ∨ ψ ⟨q, hQA q hq⟩ = sb := by
    intro q hq
    rcases hQ q hq with h | h
    · exact Or.inl (hψR q _ h)
    · right
      have h1 := hψR _ (A.mul_mem (hQA _ hsQ) (hQA q hq)) h
      have h2 : ψ ⟨(s : G) * q, A.mul_mem (hQA _ hsQ) (hQA q hq)⟩ =
          ψ ⟨s, hQA _ hsQ⟩ * ψ ⟨q, hQA q hq⟩ := map_mul ψ ⟨s, hQA _ hsQ⟩ ⟨q, hQA q hq⟩
      rw [h1, hψs] at h2
      rw [← hsbinv]
      exact (eq_inv_of_mul_eq_one_right h2.symm)
  have hsbEperm : (sb : Equiv.Perm (fixSet Ω R)) ∈ Eperm := ⟨sb, hsbE, rfl⟩
  have hQEt : Q' ≤ Et := by
    intro q hq
    refine Subgroup.mem_inf.mpr ⟨(Subgroup.mem_inf.mp hq).2, ?_⟩
    change ψ q ∈ Eperm
    rcases hψQ q hq with h | h
    · rw [show q = ⟨q, hQA q hq⟩ from rfl, h]
      exact one_mem _
    · rw [show q = ⟨q, hQA q hq⟩ from rfl, h]
      exact hsbEperm
  have hQi := C.fusionIsSylowIn_kerC hP i
  have hQsyl : fusionIsSylowIn 2 Q' Et := by
    refine ⟨hQEt, hQi.2.1.comap_of_injective A.subtype A.subtype_injective,
      fun X hXEt hX hQX => ?_⟩
    have h1 : X.map A.subtype ≤ C.kerC i := by
      rintro _ ⟨x, hx, rfl⟩
      exact (Subgroup.mem_inf.mp (hXEt hx)).1
    have h2 : C.calP ⊓ C.kerC i ≤ X.map A.subtype := fun q hq =>
      ⟨⟨q, hQA q hq⟩, hQX hq, rfl⟩
    have h3' := hQi.2.2 _ h1 (hX.map A.subtype) h2
    ext x
    constructor
    · intro hx
      have : (x : G) ∈ X.map A.subtype := ⟨x, hx, rfl⟩
      rw [h3'] at this
      exact this
    · intro hx
      exact hQX hx
  have himg : Et.map ψ = Eperm := by
    refine le_antisymm (Subgroup.map_le_iff_le_comap.mpr inf_le_right) ?_
    rintro _ ⟨e, he, rfl⟩
    obtain ⟨c, hcC, hce⟩ := mem_centralizerImage.mp e.2
    have hcA : c ∈ A := centralizer_le_stabilizer_fixSet R hcC
    have hcfix : ∀ ω : fixSet Ω R, (s : G) • (ω : Ω) = ω → DK.coord ω k = DK.coord a k →
        c • (ω : Ω) = ω := fun ω hsω hωk => by
      rw [← hce ω]
      exact congrArg Subtype.val (hEfix e he ω hsω hωk)
    have hcK : c ∈ C.kerC i := by
      refine Subgroup.mem_inf.mpr ⟨Subgroup.mem_inf.mpr ⟨?_, ?_⟩, ?_⟩
      · exact mem_stabilizer_iff.mpr (hcfix a hsα rfl)
      · exact mem_stabilizer_iff.mpr (hcfix b hsβ (hpar ⟨γK, hγKΔ⟩).2)
      · rw [mem_fixingSubgroup_iff]
        rintro _ ⟨δ, rfl, hδ⟩
        set δF : fixSet Ω R := ⟨δ, (hRH δ).mpr hδ⟩
        have hδF : δF ∈ holtDelta (centralizerImage Ω R) (fixSet Ω R) a b :=
          (hS.mem_holtDelta_centralizerImage_iff hR h3 hab).mpr δ.2
        exact hcfix δF (hsδ ⟨δF, hδF⟩) (hpar ⟨δF, hδF⟩).1
    refine ⟨⟨c, hcA⟩, Subgroup.mem_inf.mpr ⟨hcK, ?_⟩, ?_⟩
    · change ψ ⟨c, hcA⟩ ∈ Eperm
      have : ψ ⟨c, hcA⟩ = (e : Equiv.Perm (fixSet Ω R)) :=
        Equiv.ext fun ω => Subtype.ext (by rw [coe_inducedHom_apply, hce])
      rw [this]
      exact ⟨e, he, rfl⟩
    · exact Equiv.ext fun ω => Subtype.ext (by rw [coe_inducedHom_apply]; exact (hce ω).symm)
  have hmap := fusionIsSylowIn_map ψ hQsyl
  rw [himg] at hmap
  have heq : Q'.map ψ = Eperm := (hmap.2.2 _ le_rfl (hE2.map _) hmap.1).symm
  have hcardQ : Nat.card (Q'.map ψ) ≤ 2 := by
    have hsub : (Q'.map ψ : Set (Equiv.Perm (fixSet Ω R))) ⊆
        {1, (sb : Equiv.Perm (fixSet Ω R))} := by
      rintro _ ⟨q, hq, rfl⟩
      rcases hψQ q hq with h | h
      · rw [show q = ⟨q, hQA q hq⟩ from rfl, h]
        exact Set.mem_insert _ _
      · rw [show q = ⟨q, hQA q hq⟩ from rfl, h]
        exact Set.mem_insert_of_mem _ rfl
    calc Nat.card (Q'.map ψ) = (Q'.map ψ : Set (Equiv.Perm (fixSet Ω R))).ncard :=
          (Nat.card_coe_set_eq _).symm
      _ ≤ ({1, (sb : Equiv.Perm (fixSet Ω R))} : Set (Equiv.Perm (fixSet Ω R))).ncard :=
          Set.ncard_le_ncard hsub (Set.toFinite _)
      _ ≤ 2 := Set.ncard_insert_le _ _ |>.trans (by rw [Set.ncard_singleton])
  have hcardE : 4 ≤ Nat.card Eperm := by
    rw [hEpermdef, Subgroup.card_map_of_injective (centralizerImage Ω R).subtype_injective]
    exact hE4
  rw [heq] at hcardQ
  omega

end AltConfig

end CFSG.Holt.H78
