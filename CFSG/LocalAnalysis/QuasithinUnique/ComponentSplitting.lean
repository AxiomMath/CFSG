module

public import CFSG.LocalAnalysis.QuasithinUnique.Defs

public section

namespace CFSG.QuasithinUnique

open CFSG.Open
open scoped Pointwise commutatorElement

variable {G : Type*} [Group G]

namespace ComponentSplitting

theorem mem_sup_iff_of_commute {A B : Subgroup G} (h : ∀ a ∈ A, ∀ b ∈ B, a * b = b * a) {x : G} :
    x ∈ A ⊔ B ↔ ∃ a ∈ A, ∃ b ∈ B, a * b = x := by
  have hle : A ≤ Subgroup.normalizer (B : Set G) := by
    refine fun a ha => Subgroup.centralizer_le_normalizer _ ?_
    rw [Subgroup.mem_centralizer_iff]
    exact fun b hb => (h a ha b hb).symm
  have := Subgroup.coe_mul_of_left_le_normalizer_right A B hle
  have hx : x ∈ A ⊔ B ↔ x ∈ ((A : Set G) * (B : Set G)) := by
    rw [← this]; rfl
  rw [hx, Set.mem_mul]
  simp

theorem mem_of_sq_eq_one_of_mem_normalizer [Finite G] {P L : Subgroup G} (hP : IsSylowTwoOf P L)
    {x : G} (hxL : x ∈ L) (hxN : x ∈ Subgroup.normalizer (P : Set G)) (hx2 : x ^ 2 = 1) :
    x ∈ P := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨hPL, hP2, hodd⟩ := hP
  have hxp : IsPGroup 2 (Subgroup.zpowers x) := by
    rintro ⟨g, hg⟩
    obtain ⟨m, rfl⟩ := Subgroup.mem_zpowers_iff.1 hg
    refine ⟨1, Subtype.ext ?_⟩
    simp only [pow_one, Subgroup.coe_pow, OneMemClass.coe_one]
    rw [← zpow_natCast, ← zpow_mul, mul_comm, zpow_mul]
    simp [hx2]
  have hle : Subgroup.zpowers x ≤ Subgroup.normalizer (P : Set G) :=
    (Subgroup.zpowers_le).2 hxN
  have hQ : IsPGroup 2 ↥(P ⊔ Subgroup.zpowers x) := hP2.to_sup_of_normal_left' hxp hle
  have hQL : P ⊔ Subgroup.zpowers x ≤ L := sup_le hPL ((Subgroup.zpowers_le).2 hxL)
  have hPQ : P ≤ P ⊔ Subgroup.zpowers x := le_sup_left
  have h1 := Subgroup.relIndex_mul_relIndex P (P ⊔ Subgroup.zpowers x) L hPQ hQL
  have hodd0 : ¬ 2 ∣ P.relIndex L := hodd
  have hodd' : ¬ 2 ∣ P.relIndex (P ⊔ Subgroup.zpowers x) := fun h2 =>
    hodd0 (h1 ▸ Dvd.dvd.mul_right h2 _)
  obtain ⟨k, hk⟩ := (IsPGroup.iff_card).1 hQ
  have hdvd : P.relIndex (P ⊔ Subgroup.zpowers x) ∣ 2 ^ k := hk ▸ Subgroup.index_dvd_card _
  have hcop : Nat.Coprime (P.relIndex (P ⊔ Subgroup.zpowers x)) (2 ^ k) :=
    Nat.Coprime.pow_right _ ((Nat.Prime.coprime_iff_not_dvd Nat.prime_two).2 hodd').symm
  have h2 : P.relIndex (P ⊔ Subgroup.zpowers x) = 1 := hcop.eq_one_of_dvd hdvd
  have hQP : P ⊔ Subgroup.zpowers x ≤ P := Subgroup.relIndex_eq_one.1 h2
  exact hQP (Subgroup.mem_sup_right (Subgroup.mem_zpowers x))

theorem eq_of_conj_eq_of_centerless {L : Subgroup G}
    (hL : L ⊓ Subgroup.centralizer (L : Set G) = ⊥) {l l' : G} (hl : l ∈ L) (hl' : l' ∈ L)
    (h : ∀ x ∈ L, l⁻¹ * x * l = l'⁻¹ * x * l') : l = l' := by
  have hc : l * l'⁻¹ ∈ L ⊓ Subgroup.centralizer (L : Set G) := by
    refine Subgroup.mem_inf.2 ⟨L.mul_mem hl (L.inv_mem hl'), ?_⟩
    rw [Subgroup.mem_centralizer_iff]
    intro x hx
    have hx' := h x hx
    calc x * (l * l'⁻¹) = l * (l⁻¹ * x * l) * l'⁻¹ := by group
      _ = l * (l'⁻¹ * x * l') * l'⁻¹ := by rw [hx']
      _ = (l * l'⁻¹) * x := by group
  rw [hL, Subgroup.mem_bot, mul_inv_eq_one] at hc
  exact hc

theorem exists_unique_inner_hom {U L : Subgroup G}
    (hL : L ⊓ Subgroup.centralizer (L : Set G) = ⊥)
    (hinner : ∀ u ∈ U, ∃ l ∈ L, ∀ x ∈ L, u⁻¹ * x * u = l⁻¹ * x * l) :
    ∃! π : ↥U →* ↥L, ∀ (u : U) (x : G), x ∈ L →
      (u : G)⁻¹ * x * u = ((π u : L) : G)⁻¹ * x * ((π u : L) : G) := by
  choose f hfL hf using fun u : U => hinner u u.2
  have hmul : ∀ u v : U, f (u * v) = f u * f v := by
    intro u v
    refine eq_of_conj_eq_of_centerless hL (hfL _) (L.mul_mem (hfL u) (hfL v)) fun x hx => ?_
    rw [← hf (u * v) x hx]
    have h2 := hf v ((f u)⁻¹ * x * f u)
      (L.mul_mem (L.mul_mem (L.inv_mem (hfL u)) hx) (hfL u))
    calc ((u * v : U) : G)⁻¹ * x * ((u * v : U) : G)
        = (v : G)⁻¹ * ((u : G)⁻¹ * x * u) * v := by simp only [Subgroup.coe_mul]; group
      _ = (v : G)⁻¹ * ((f u)⁻¹ * x * f u) * v := by rw [hf u x hx]
      _ = (f v)⁻¹ * ((f u)⁻¹ * x * f u) * f v := h2
      _ = (f u * f v)⁻¹ * x * (f u * f v) := by group
  refine ⟨{ toFun := fun u => ⟨f u, hfL u⟩, map_one' := ?_, map_mul' := ?_ }, ?_, ?_⟩
  · refine Subtype.ext (eq_of_conj_eq_of_centerless hL (hfL 1) L.one_mem fun x hx => ?_)
    rw [← hf 1 x hx]
    simp
  · intro u v
    exact Subtype.ext (hmul u v)
  · intro u x hx
    exact hf u x hx
  · intro π' hπ'
    refine MonoidHom.ext fun u => Subtype.ext ?_
    have := eq_of_conj_eq_of_centerless hL (π' u).2 (hfL u) fun x hx => by
      rw [← hπ' u x hx, hf u x hx]
    exact this

theorem mem_normalizer_inf_of_conj_eq {S L : Subgroup G} {u g : G} (huS : u ∈ S)
    (huL : u ∈ Subgroup.normalizer (L : Set G)) (hgL : g ∈ L)
    (hg : ∀ x ∈ L, g⁻¹ * x * g = u⁻¹ * x * u) :
    g ∈ Subgroup.normalizer ((S ⊓ L : Subgroup G) : Set G) := by
  have hconj : ∀ h ∈ L, g * h * g⁻¹ = u * h * u⁻¹ := by
    intro h hh
    have h1 := hg (g * h * g⁻¹) (L.mul_mem (L.mul_mem hgL hh) (L.inv_mem hgL))
    calc g * h * g⁻¹ = u * (u⁻¹ * (g * h * g⁻¹) * u) * u⁻¹ := by group
      _ = u * (g⁻¹ * (g * h * g⁻¹) * g) * u⁻¹ := by rw [← h1]
      _ = u * h * u⁻¹ := by group
  rw [Subgroup.mem_normalizer_iff]
  intro h
  constructor
  · rintro ⟨hS, hL⟩
    rw [hconj h hL]
    exact ⟨S.mul_mem (S.mul_mem huS hS) (S.inv_mem huS),
      (Subgroup.mem_normalizer_iff.1 huL h).1 hL⟩
  · rintro ⟨hS, hL⟩
    have hhL : h ∈ L := by
      have := L.mul_mem (L.mul_mem (L.inv_mem hgL) hL) hgL
      simpa [mul_assoc] using this
    rw [hconj h hhL] at hS
    refine ⟨?_, hhL⟩
    have := S.mul_mem (S.mul_mem (S.inv_mem huS) hS) huS
    simpa [mul_assoc] using this

theorem isElemAbelian_range_of_hom {U : Subgroup G} {X : Type*} [Group X]
    (hU : IsElemAbelian 2 U) (f : ↥U →* X) : IsElemAbelian 2 f.range := by
  refine ⟨⟨⟨?_⟩⟩, ?_⟩
  · rintro ⟨_, u, rfl⟩ ⟨_, v, rfl⟩
    apply Subtype.ext
    simp only [Subgroup.coe_mul, ← map_mul]
    congr 1
    exact hU.1.is_comm.comm u v
  · rintro _ ⟨u, rfl⟩
    rw [← map_pow]
    have : u ^ 2 = 1 := Subtype.ext (hU.2 u u.2)
    rw [this, map_one]

theorem inner_elementary_component_projections_aux [Finite G] {H S U L : Subgroup G}
    (hS : IsSylowTwoOf S H) (hUS : U ≤ S) (hU : IsElemAbelian 2 U)
    (hcl : ∀ a ∈ U, ∀ g ∈ H, g⁻¹ * a * g ∈ S → g⁻¹ * a * g ∈ U)
    (hLH : L ≤ H) (hLc : L ⊓ Subgroup.centralizer (L : Set G) = ⊥)
    (hP : IsSylowTwoOf (S ⊓ L) L) (hUL : U ≤ Subgroup.normalizer (L : Set G))
    (π : ↥U →* ↥L)
    (hπ : ∀ (u : U) (x : G), x ∈ L →
      (u : G)⁻¹ * x * u = ((π u : L) : G)⁻¹ * x * ((π u : L) : G)) :
    (∀ u : U, ((π u : L) : G) * ((u : G) * ((π u : L) : G)⁻¹) = u) ∧
    ∃ A B : Subgroup G,
      (∀ x, x ∈ A ↔ ∃ u : U, ((π u : L) : G) = x) ∧
      (∀ x, x ∈ B ↔ ∃ u : U, (u : G) * ((π u : L) : G)⁻¹ = x) ∧
      A ≤ S ⊓ L ∧ B ≤ S ⊓ (H ⊓ Subgroup.centralizer (L : Set G)) ∧
      IsElemAbelian 2 A ∧ IsElemAbelian 2 B ∧
      (∀ a ∈ A, ∀ b ∈ B, a * b = b * a) ∧ A ⊓ B = ⊥ ∧ U ≤ A ⊔ B ∧
      (∀ a ∈ A, ∃ b ∈ B, a * b ∈ U) ∧ (∀ b ∈ B, ∃ a ∈ A, a * b ∈ U) ∧
      ∀ a ∈ A, ∀ l ∈ L, l⁻¹ * a * l ∈ S ⊓ L → l⁻¹ * a * l ∈ A := by
  obtain ⟨p, hp⟩ : ∃ p : ↥U → G, ∀ u, p u = ((π u : L) : G) :=
    ⟨fun u => ((π u : L) : G), fun _ => rfl⟩
  have hpL : ∀ u : U, p u ∈ L := fun u => by rw [hp]; exact (π u).2
  have hpmul : ∀ u v : U, p (u * v) = p u * p v := fun u v => by simp [hp]
  have hpone : p 1 = 1 := by simp [hp]
  have hπ' : ∀ (u : U) (x : G), x ∈ L → (u : G)⁻¹ * x * u = (p u)⁻¹ * x * p u :=
    fun u x hx => by rw [hp]; exact hπ u x hx
  have hsq : ∀ u : U, u * u = 1 := fun u => Subtype.ext (by simpa [sq] using hU.2 u u.2)
  have hpsq : ∀ u : U, p u * p u = 1 := fun u => by rw [← hpmul, hsq, hpone]
  have hcentral : ∀ (u : U) (x : G), x ∈ L →
      (u : G) * (p u)⁻¹ * x = x * ((u : G) * (p u)⁻¹) := by
    intro u x hx
    have key : ((u : G) * (p u)⁻¹)⁻¹ * x * ((u : G) * (p u)⁻¹) = x := by
      calc ((u : G) * (p u)⁻¹)⁻¹ * x * ((u : G) * (p u)⁻¹)
          = p u * ((u : G)⁻¹ * x * u) * (p u)⁻¹ := by group
        _ = p u * ((p u)⁻¹ * x * p u) * (p u)⁻¹ := by rw [hπ' u x hx]
        _ = x := by group
    calc (u : G) * (p u)⁻¹ * x
        = (u : G) * (p u)⁻¹ * (((u : G) * (p u)⁻¹)⁻¹ * x * ((u : G) * (p u)⁻¹)) := by rw [key]
      _ = x * ((u : G) * (p u)⁻¹) := by group
  have hpP : ∀ u : U, p u ∈ S ⊓ L := by
    intro u
    have hnorm : p u ∈ Subgroup.normalizer ((S ⊓ L : Subgroup G) : Set G) :=
      mem_normalizer_inf_of_conj_eq (hUS u.2) (hUL u.2) (hpL u) fun x hx => (hπ' u x hx).symm
    have hsq' : p u ^ 2 = 1 := by rw [sq]; exact hpsq u
    exact mem_of_sq_eq_one_of_mem_normalizer hP (hpL u) hnorm hsq'
  obtain ⟨ρ, hρ⟩ : ∃ ρ : ↥U →* G, ∀ u, ρ u = p u :=
    ⟨L.subtype.comp π, fun u => (hp u).symm⟩
  obtain ⟨σ, hσ⟩ : ∃ σ : ↥U →* G, ∀ u, σ u = (u : G) * (p u)⁻¹ := by
    refine ⟨{ toFun := fun u => (u : G) * (p u)⁻¹, map_one' := ?_, map_mul' := ?_ },
      fun _ => rfl⟩
    · simp [hpone]
    · intro u v
      have h := hcentral v (p u)⁻¹ (L.inv_mem (hpL u))
      calc ((u * v : U) : G) * (p (u * v))⁻¹ = (u : G) * ((v : G) * (p v)⁻¹ * (p u)⁻¹) := by
            rw [hpmul]; simp only [Subgroup.coe_mul]; group
        _ = (u : G) * ((p u)⁻¹ * ((v : G) * (p v)⁻¹)) := by rw [h]
        _ = (u : G) * (p u)⁻¹ * ((v : G) * (p v)⁻¹) := by group
  have hσS : ∀ u : U, σ u ∈ S := fun u => by
    rw [hσ]
    exact S.mul_mem (hUS u.2) (S.inv_mem (hpP u).1)
  have hσC : ∀ u : U, σ u ∈ Subgroup.centralizer (L : Set G) := fun u => by
    rw [Subgroup.mem_centralizer_iff]
    intro x hx
    rw [hσ]
    exact (hcentral u x hx).symm
  have hdecomp' : ∀ u : U, p u * ((u : G) * (p u)⁻¹) = (u : G) := fun u =>
    calc p u * ((u : G) * (p u)⁻¹) = (u : G) * (p u)⁻¹ * p u := (hcentral u (p u) (hpL u)).symm
      _ = u := by group
  have hdecomp : ∀ u : U, ρ u * σ u = (u : G) := fun u => by
    rw [hρ, hσ]
    exact hdecomp' u
  refine ⟨fun u => by rw [← hp]; exact hdecomp' u, ρ.range, σ.range, ?_, ?_, ?_, ?_,
    isElemAbelian_range_of_hom hU ρ, isElemAbelian_range_of_hom hU σ, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro x
    simp only [MonoidHom.mem_range, hρ, hp]
  · intro x
    simp only [MonoidHom.mem_range, hσ, hp]
  · rintro _ ⟨u, rfl⟩
    rw [hρ]
    exact hpP u
  · rintro _ ⟨u, rfl⟩
    exact ⟨hσS u, hS.1 (hσS u), hσC u⟩
  · rintro _ ⟨u, rfl⟩ _ ⟨v, rfl⟩
    rw [hρ]
    exact Subgroup.mem_centralizer_iff.1 (hσC v) _ (hpL u)
  · rw [eq_bot_iff]
    rintro x ⟨⟨u, rfl⟩, ⟨v, hv⟩⟩
    have hxL : ρ u ∈ L ⊓ Subgroup.centralizer (L : Set G) := by
      refine Subgroup.mem_inf.2 ⟨by rw [hρ]; exact hpL u, ?_⟩
      rw [← hv]
      exact hσC v
    rwa [hLc] at hxL
  · intro u hu
    have h1 : ρ ⟨u, hu⟩ ∈ ρ.range := ⟨⟨u, hu⟩, rfl⟩
    have h2 : σ ⟨u, hu⟩ ∈ σ.range := ⟨⟨u, hu⟩, rfl⟩
    have := Subgroup.mul_mem_sup h1 h2
    rwa [hdecomp] at this
  · rintro _ ⟨u, rfl⟩
    exact ⟨σ u, ⟨u, rfl⟩, by rw [hdecomp]; exact u.2⟩
  · rintro _ ⟨u, rfl⟩
    exact ⟨ρ u, ⟨u, rfl⟩, by rw [hdecomp]; exact u.2⟩
  · rintro _ ⟨u, rfl⟩ l hl hlP
    rw [hρ] at hlP ⊢
    have hmL : l⁻¹ * p u * l ∈ L := L.mul_mem (L.mul_mem (L.inv_mem hl) (hpL u)) hl
    have hc1 := hcentral u l⁻¹ (L.inv_mem hl)
    have hv_eq : l⁻¹ * (u : G) * l = ((u : G) * (p u)⁻¹) * (l⁻¹ * p u * l) := by
      calc l⁻¹ * (u : G) * l = (l⁻¹ * ((u : G) * (p u)⁻¹)) * (p u * l) := by group
        _ = ((u : G) * (p u)⁻¹ * l⁻¹) * (p u * l) := by rw [hc1]
        _ = ((u : G) * (p u)⁻¹) * (l⁻¹ * p u * l) := by group
    have hvS : l⁻¹ * (u : G) * l ∈ S := by
      rw [hv_eq]
      exact S.mul_mem (by rw [← hσ]; exact hσS u) hlP.1
    have hvU : l⁻¹ * (u : G) * l ∈ U := hcl u u.2 l (hLH hl) hvS
    have hpv : p ⟨_, hvU⟩ = l⁻¹ * p u * l := by
      refine eq_of_conj_eq_of_centerless hLc (hpL _) hmL fun x hx => ?_
      have hy : l * x * l⁻¹ ∈ L := L.mul_mem (L.mul_mem hl hx) (L.inv_mem hl)
      have h1 := hπ' u (l * x * l⁻¹) hy
      calc (p ⟨_, hvU⟩)⁻¹ * x * p ⟨_, hvU⟩ = (l⁻¹ * (u : G) * l)⁻¹ * x * (l⁻¹ * (u : G) * l) :=
            (hπ' ⟨_, hvU⟩ x hx).symm
        _ = l⁻¹ * ((u : G)⁻¹ * (l * x * l⁻¹) * u) * l := by group
        _ = l⁻¹ * ((p u)⁻¹ * (l * x * l⁻¹) * p u) * l := by rw [h1]
        _ = (l⁻¹ * p u * l)⁻¹ * x * (l⁻¹ * p u * l) := by group
    exact ⟨⟨_, hvU⟩, by rw [hρ, hpv]⟩

end ComponentSplitting

theorem irreducible_subdirect_product_splitting {p : ℕ} [Fact p.Prime] {A B N U : Subgroup G}
    (hcomm : ∀ a ∈ A, ∀ b ∈ B, a * b = b * a) (hdisj : A ⊓ B = ⊥)
    (hA : IsElemAbelian p A) (hrank : p ^ 2 ≤ Nat.card A)
    (hNA : N ≤ Subgroup.normalizer (A : Set G)) (hNB : N ≤ Subgroup.centralizer (B : Set G))
    (hirr : ∀ V : Subgroup G, V ≤ A → N ≤ Subgroup.normalizer (V : Set G) → V = ⊥ ∨ V = A)
    (hUle : U ≤ A ⊔ B) (hUN : N ≤ Subgroup.normalizer (U : Set G))
    (hproj : ∀ a ∈ A, ∃ b ∈ B, a * b ∈ U) :
    A ≤ U ∧ (U = A ⊔ (U ⊓ B) ∧ A ⊓ (U ⊓ B) = ⊥ ∧ ∀ a ∈ A, ∀ b ∈ U ⊓ B, a * b = b * a) := by
  have hp : 2 ≤ p := (Fact.out : p.Prime).two_le
  have hfixB : ∀ n ∈ N, ∀ b ∈ B, n * b * n⁻¹ = b := by
    intro n hn b hb
    have := Subgroup.mem_centralizer_iff.1 (hNB hn) b hb
    rw [← this, mul_inv_cancel_right]
  have hWN : N ≤ Subgroup.normalizer ((U ⊓ A : Subgroup G) : Set G) :=
    fun n hn => Subgroup.inf_normalizer_le_normalizer_inf ⟨hUN hn, hNA hn⟩
  have hW : U ⊓ A = ⊥ ∨ U ⊓ A = A := hirr _ inf_le_right hWN
  have hAU : A ≤ U := by
    rcases hW with hW | hW
    · exfalso
      have hcentA : ∀ n ∈ N, ∀ a ∈ A, n * a * n⁻¹ = a := by
        intro n hn a ha
        obtain ⟨b, hb, hab⟩ := hproj a ha
        have hnu : n * (a * b) * n⁻¹ ∈ U := (Subgroup.mem_normalizer_iff.1 (hUN hn) (a * b)).1 hab
        have hx : a⁻¹ * (n * a * n⁻¹) ∈ A :=
          A.mul_mem (A.inv_mem ha) ((Subgroup.mem_normalizer_iff.1 (hNA hn) a).1 ha)
        have key : (a * b)⁻¹ * (n * (a * b) * n⁻¹) = a⁻¹ * (n * a * n⁻¹) := by
          have e1 : n * (a * b) * n⁻¹ = (n * a * n⁻¹) * (n * b * n⁻¹) := by group
          rw [e1, hfixB n hn b hb]
          have e2 := hcomm _ hx b hb
          calc (a * b)⁻¹ * (n * a * n⁻¹ * b) = b⁻¹ * (a⁻¹ * (n * a * n⁻¹)) * b := by group
            _ = b⁻¹ * (b * (a⁻¹ * (n * a * n⁻¹))) := by rw [← e2]; group
            _ = a⁻¹ * (n * a * n⁻¹) := by group
        have hmemU : a⁻¹ * (n * a * n⁻¹) ∈ U := by
          rw [← key]
          exact U.mul_mem (U.inv_mem hab) hnu
        have hbot : a⁻¹ * (n * a * n⁻¹) ∈ U ⊓ A := ⟨hmemU, hx⟩
        rw [hW, Subgroup.mem_bot] at hbot
        calc n * a * n⁻¹ = a * (a⁻¹ * (n * a * n⁻¹)) := by group
          _ = a := by rw [hbot, mul_one]
      have hNcent : N ≤ Subgroup.centralizer (A : Set G) := by
        intro n hn
        rw [Subgroup.mem_centralizer_iff]
        intro a ha
        have := hcentA n hn a ha
        rw [mul_inv_eq_iff_eq_mul] at this
        exact this.symm
      have hsub : ∀ V : Subgroup G, V ≤ A → V = ⊥ ∨ V = A := fun V hVA =>
        hirr V hVA (hNcent.trans ((Subgroup.centralizer_le (SetLike.coe_subset_coe.2 hVA)).trans
          (Subgroup.centralizer_le_normalizer _)))
      have hAne : A ≠ ⊥ := by
        intro h
        rw [h, Subgroup.card_bot] at hrank
        nlinarith
      obtain ⟨⟨a, haA⟩, ha1⟩ := (Subgroup.ne_bot_iff_exists_ne_one).1 hAne
      have ha1' : a ≠ 1 := fun h => ha1 (Subtype.ext h)
      have hord : orderOf a = p := orderOf_eq_prime (hA.2 a haA) ha1'
      rcases hsub (Subgroup.zpowers a) ((Subgroup.zpowers_le).2 haA) with hV | hV
      · have : a ∈ Subgroup.zpowers a := Subgroup.mem_zpowers a
        rw [hV, Subgroup.mem_bot] at this
        exact ha1' this
      · have hc : Nat.card A = p := by
          rw [← hV, Nat.card_zpowers, hord]
        rw [hc] at hrank
        nlinarith
    · exact hW ▸ inf_le_left
  refine ⟨hAU, ?_, ?_, ?_⟩
  · apply le_antisymm
    · intro u hu
      obtain ⟨a, ha, b, hb, rfl⟩ := (ComponentSplitting.mem_sup_iff_of_commute hcomm).1 (hUle hu)
      have hbU : b ∈ U := by
        have := U.mul_mem (U.inv_mem (hAU ha)) hu
        simpa using this
      exact Subgroup.mul_mem_sup ha ⟨hbU, hb⟩
    · exact sup_le hAU inf_le_left
  · rw [eq_bot_iff]
    intro x hx
    have : x ∈ A ⊓ B := ⟨hx.1, hx.2.2⟩
    rw [hdisj] at this
    exact this
  · intro a ha b hb
    exact hcomm a ha b hb.2

theorem inner_elementary_component_projections [Finite G] {H S U L : Subgroup G}
    (hS : IsSylowTwoOf S H) (hUS : U ≤ S) (hU : IsElemAbelian 2 U)
    (hcl : ∀ a ∈ U, ∀ g ∈ H, g⁻¹ * a * g ∈ S → g⁻¹ * a * g ∈ U)
    (hLH : L ≤ H) (hLc : L ⊓ Subgroup.centralizer (L : Set G) = ⊥)
    (hP : IsSylowTwoOf (S ⊓ L) L) (hUL : U ≤ Subgroup.normalizer (L : Set G))
    (hinner : ∀ u ∈ U, ∃ l ∈ L, ∀ x ∈ L, u⁻¹ * x * u = l⁻¹ * x * l) :
    ∃ π : ↥U →* ↥L,
      (∀ (u : U) (x : G), x ∈ L →
        (u : G)⁻¹ * x * u = ((π u : L) : G)⁻¹ * x * ((π u : L) : G)) ∧
      (∀ π' : ↥U →* ↥L, (∀ (u : U) (x : G), x ∈ L →
        (u : G)⁻¹ * x * u = ((π' u : L) : G)⁻¹ * x * ((π' u : L) : G)) → π' = π) ∧
      (∀ u : U, ((π u : L) : G) * ((u : G) * ((π u : L) : G)⁻¹) = u) ∧
      ∃ A B : Subgroup G,
        (∀ x, x ∈ A ↔ ∃ u : U, ((π u : L) : G) = x) ∧
        (∀ x, x ∈ B ↔ ∃ u : U, (u : G) * ((π u : L) : G)⁻¹ = x) ∧
        A ≤ S ⊓ L ∧ B ≤ S ⊓ (H ⊓ Subgroup.centralizer (L : Set G)) ∧
        IsElemAbelian 2 A ∧ IsElemAbelian 2 B ∧
        (∀ a ∈ A, ∀ b ∈ B, a * b = b * a) ∧ A ⊓ B = ⊥ ∧ U ≤ A ⊔ B ∧
        (∀ a ∈ A, ∃ b ∈ B, a * b ∈ U) ∧ (∀ b ∈ B, ∃ a ∈ A, a * b ∈ U) ∧
        ∀ a ∈ A, ∀ l ∈ L, l⁻¹ * a * l ∈ S ⊓ L → l⁻¹ * a * l ∈ A := by
  obtain ⟨π, hπ, huniq⟩ := ComponentSplitting.exists_unique_inner_hom hLc hinner
  exact ⟨π, hπ, huniq,
    ComponentSplitting.inner_elementary_component_projections_aux hS hUS hU hcl hLH hLc hP hUL π hπ⟩

theorem confined_inner_rank_one_component_splitting [Finite G]
    {H M S U L V A C : Subgroup G} {w : G}
    (hS : IsSylowTwoOf S H) (hUS : U ≤ S) (hU : IsElemAbelian 2 U)
    (hcl : ∀ a ∈ U, ∀ g ∈ H, g⁻¹ * a * g ∈ S → g⁻¹ * a * g ∈ U)
    (hMU : M ≤ Subgroup.normalizer (U : Set G))
    (hLH : L ≤ H) (hLc : L ⊓ Subgroup.centralizer (L : Set G) = ⊥)
    (hP : IsSylowTwoOf (S ⊓ L) L) (hUL : U ≤ Subgroup.normalizer (L : Set G))
    (hinner : ∀ u ∈ U, ∃ l ∈ L, ∀ x ∈ L, u⁻¹ * x * u = l⁻¹ * x * l)
    (hLU : ⁅L, U⁆ ≠ ⊥)
    (hV : V = Subgroup.closure {x | x ∈ S ⊓ L ∧ x ^ 2 = 1}) (hVcard : 4 ≤ Nat.card V)
    (htrans : ∀ a ∈ V, a ≠ 1 → ∀ b ∈ V, b ≠ 1 →
      ∃ n ∈ L ⊓ Subgroup.normalizer (V : Set G), n⁻¹ * a * n = b)
    (hcyc : ∃ g ∈ L ⊓ Subgroup.normalizer (V : Set G),
      ∀ n ∈ L ⊓ Subgroup.normalizer (V : Set G), ∃ k : ℕ, ∀ x ∈ V,
        n⁻¹ * x * n = (g ^ k)⁻¹ * x * g ^ k)
    (hwU : w ∈ U)
    (hconf : ∀ R : Subgroup G, IsPGroup 2 R → w ∈ R → Subgroup.normalizer (R : Set G) ≤ M)
    (hA : A = U ⊓ L) (hC : C = U ⊓ Subgroup.centralizer (L : Set G)) :
    A = V ∧ (U = A ⊔ C ∧ A ⊓ C = ⊥ ∧ ∀ a ∈ A, ∀ c ∈ C, a * c = c * a) ∧
      L ⊓ Subgroup.normalizer (A : Set G) ≤ M ∧
      (∀ n ∈ L ⊓ Subgroup.normalizer (A : Set G), ∀ c ∈ C, n⁻¹ * c * n = c) ∧
      (∀ a ∈ A, a ≠ 1 → ∀ b ∈ A, b ≠ 1 →
        ∃ n ∈ L ⊓ Subgroup.normalizer (A : Set G), n⁻¹ * a * n = b) ∧
      (∀ n ∈ L ⊓ Subgroup.normalizer (A : Set G), ∀ a ∈ A, a ≠ 1 → n⁻¹ * a * n = a →
        ∀ x ∈ U, n⁻¹ * x * n = x) ∧
      (∃ g ∈ L ⊓ Subgroup.normalizer (A : Set G),
        ∀ n ∈ L ⊓ Subgroup.normalizer (A : Set G), ∃ k : ℕ, ∀ x ∈ U,
          n⁻¹ * x * n = (g ^ k)⁻¹ * x * g ^ k) := by
  obtain ⟨π, hπ, -, -, A₀, B, hA₀, hB, hAP, hBS, hAel, hBel, hAB, hABbot, hUAB, hprojA, hprojB,
    hAcl⟩ := inner_elementary_component_projections hS hUS hU hcl hLH hLc hP hUL hinner
  have hVP : V ≤ S ⊓ L := by
    rw [hV]
    exact (Subgroup.closure_le _).2 fun x hx => hx.1
  have hA₀ne : A₀ ≠ ⊥ := by
    intro hbot
    apply hLU
    have hπ1 : ∀ u : U, ((π u : L) : G) = 1 := by
      intro u
      have := (hA₀ _).2 ⟨u, rfl⟩
      rwa [hbot, Subgroup.mem_bot] at this
    refine Subgroup.commutator_eq_bot_iff_le_centralizer.2 fun x hx => ?_
    rw [Subgroup.mem_centralizer_iff]
    intro u hu
    have h := hπ ⟨u, hu⟩ x hx
    rw [hπ1 ⟨u, hu⟩] at h
    simp only [inv_one, one_mul, mul_one] at h
    have h2 : x * u = u * x := by
      calc x * u = u * (u⁻¹ * x * u) := by group
        _ = u * x := by rw [h]
    exact h2.symm
  have hA₀V : A₀ ≤ V := by
    intro a ha
    rw [hV]
    exact Subgroup.subset_closure ⟨hAP ha, hAel.2 a ha⟩
  have hVA₀ : V ≤ A₀ := by
    obtain ⟨⟨a₀, ha₀⟩, ha₀1⟩ := Subgroup.ne_bot_iff_exists_ne_one.1 hA₀ne
    have ha₀1' : a₀ ≠ 1 := fun h => ha₀1 (Subtype.ext h)
    intro b hbV
    by_cases hb1 : b = 1
    · rw [hb1]; exact A₀.one_mem
    · obtain ⟨n, hn, hnab⟩ := htrans a₀ (hA₀V ha₀) ha₀1' b hbV hb1
      have := hAcl a₀ ha₀ n hn.1 (by rw [hnab]; exact hVP hbV)
      rwa [hnab] at this
  have hAV : V = A₀ := le_antisymm hVA₀ hA₀V
  subst hAV
  have hBC : ∀ b ∈ B, b ∈ Subgroup.centralizer (L : Set G) := fun b hb => (hBS hb).2.2
  have hBcomm : ∀ m ∈ L, ∀ b ∈ B, m * b * m⁻¹ = b := by
    intro m hm b hb
    rw [Subgroup.mem_centralizer_iff.1 (hBC b hb) m hm, mul_inv_cancel_right]
  have hR2 : IsPGroup 2 ↥(V ⊔ B) := by
    rintro ⟨g, hg⟩
    obtain ⟨a, ha, b, hb, rfl⟩ := (ComponentSplitting.mem_sup_iff_of_commute hAB).1 hg
    refine ⟨1, Subtype.ext ?_⟩
    simp only [pow_one, Subgroup.coe_pow, OneMemClass.coe_one]
    have hc : Commute a b := hAB a ha b hb
    rw [hc.mul_pow, hAel.2 a ha, hBel.2 b hb, one_mul]
  have hNM : Subgroup.normalizer ((V ⊔ B : Subgroup G) : Set G) ≤ M :=
    hconf (V ⊔ B) hR2 (hUAB hwU)
  have hNR : L ⊓ Subgroup.normalizer (V : Set G) ≤
      Subgroup.normalizer ((V ⊔ B : Subgroup G) : Set G) := by
    have key : ∀ m ∈ L ⊓ Subgroup.normalizer (V : Set G), ∀ x ∈ V ⊔ B, m * x * m⁻¹ ∈ V ⊔ B := by
      rintro m ⟨hmL, hmV⟩ x hx
      obtain ⟨a, ha, b, hb, rfl⟩ := (ComponentSplitting.mem_sup_iff_of_commute hAB).1 hx
      have h1 : m * (a * b) * m⁻¹ = (m * a * m⁻¹) * b := by
        calc m * (a * b) * m⁻¹ = (m * a * m⁻¹) * (m * b * m⁻¹) := by group
          _ = (m * a * m⁻¹) * b := by rw [hBcomm m hmL b hb]
      rw [h1]
      exact Subgroup.mul_mem_sup ((Subgroup.mem_normalizer_iff.1 hmV a).1 ha) hb
    intro n hn
    rw [Subgroup.mem_normalizer_iff]
    intro x
    refine ⟨key n hn x, fun hx => ?_⟩
    have := key n⁻¹ ((L ⊓ Subgroup.normalizer (V : Set G)).inv_mem hn) _ hx
    have e : n⁻¹ * (n * x * n⁻¹) * n⁻¹⁻¹ = x := by group
    rwa [e] at this
  have hNM' : L ⊓ Subgroup.normalizer (V : Set G) ≤ M := hNR.trans hNM
  have hirr : ∀ V' : Subgroup G, V' ≤ V → L ⊓ Subgroup.normalizer (V : Set G) ≤
      Subgroup.normalizer (V' : Set G) → V' = ⊥ ∨ V' = V := by
    intro V' hV'V hN
    by_cases hbot : V' = ⊥
    · exact Or.inl hbot
    · right
      obtain ⟨⟨a, haV'⟩, ha1⟩ := Subgroup.ne_bot_iff_exists_ne_one.1 hbot
      have ha1' : a ≠ 1 := fun h => ha1 (Subtype.ext h)
      refine le_antisymm hV'V fun b hbV => ?_
      by_cases hb1 : b = 1
      · rw [hb1]; exact V'.one_mem
      · obtain ⟨n, hn, hnab⟩ := htrans a (hV'V haV') ha1' b hbV hb1
        have := (Subgroup.mem_normalizer_iff.1
          (hN ((L ⊓ Subgroup.normalizer (V : Set G)).inv_mem hn)) a).1 haV'
        simpa [hnab] using this
  obtain ⟨hVU, hUeq, -, -⟩ := irreducible_subdirect_product_splitting (p := 2) (A := V) (B := B)
    (N := L ⊓ Subgroup.normalizer (V : Set G)) (U := U) hAB hABbot hAel (by simpa using hVcard)
    inf_le_right
    (fun n hn => Subgroup.mem_centralizer_iff.2 fun b hb =>
      (Subgroup.mem_centralizer_iff.1 (hBC b hb) n hn.1).symm)
    hirr hUAB (fun n hn => hMU (hNM' hn)) hprojA
  have hBU : B ≤ U := by
    intro b hb
    obtain ⟨a, ha, hab⟩ := hprojB b hb
    have := U.mul_mem (U.inv_mem (hVU ha)) hab
    simpa using this
  have hUVB : U = V ⊔ B := le_antisymm hUAB (sup_le hVU hBU)
  have hUL_eq : U ⊓ L = V := by
    refine le_antisymm ?_ (le_inf hVU (hVP.trans inf_le_right))
    rintro x ⟨hxU, hxL⟩
    have hx' : x ∈ V ⊔ B := by rw [← hUVB]; exact hxU
    obtain ⟨v, hv, b, hb, rfl⟩ := (ComponentSplitting.mem_sup_iff_of_commute hAB).1 hx'
    have hbL : b ∈ L := by
      have := L.mul_mem (L.inv_mem (hVP hv).2) hxL
      simpa using this
    have hb1 : b = 1 := by
      have : b ∈ L ⊓ Subgroup.centralizer (L : Set G) := Subgroup.mem_inf.2 ⟨hbL, hBC b hb⟩
      rwa [hLc, Subgroup.mem_bot] at this
    rw [hb1, mul_one]
    exact hv
  have hUC_eq : U ⊓ Subgroup.centralizer (L : Set G) = B := by
    refine le_antisymm ?_ (fun b hb => Subgroup.mem_inf.2 ⟨hBU hb, hBC b hb⟩)
    rintro x ⟨hxU, hxC⟩
    have hx' : x ∈ V ⊔ B := by rw [← hUVB]; exact hxU
    obtain ⟨v, hv, b, hb, rfl⟩ := (ComponentSplitting.mem_sup_iff_of_commute hAB).1 hx'
    have hvC : v ∈ Subgroup.centralizer (L : Set G) := by
      have := (Subgroup.centralizer (L : Set G)).mul_mem hxC
        ((Subgroup.centralizer (L : Set G)).inv_mem (hBC b hb))
      simpa using this
    have hv1 : v = 1 := by
      have : v ∈ L ⊓ Subgroup.centralizer (L : Set G) := Subgroup.mem_inf.2 ⟨(hVP hv).2, hvC⟩
      rwa [hLc, Subgroup.mem_bot] at this
    rw [hv1, one_mul]
    exact hb
  have hAeq : A = V := hA.trans hUL_eq
  have hCeq : C = B := hC.trans hUC_eq
  rw [hAeq, hCeq]
  obtain ⟨g, hgN, hg⟩ := hcyc
  refine ⟨rfl, ⟨hUVB, hABbot, hAB⟩, hNM', ?_, htrans, ?_, ⟨g, hgN, ?_⟩⟩
  · intro n hn c hc
    have h := hBcomm n⁻¹ (L.inv_mem hn.1) c hc
    simpa using h
  · intro n hn a ha ha1 hna x hx
    obtain ⟨j, hj⟩ := hg n hn
    have hnV : ∀ b ∈ V, n⁻¹ * b * n = b := by
      intro b hb
      by_cases hb1 : b = 1
      · rw [hb1]; simp
      · obtain ⟨m, hm, hmab⟩ := htrans a ha ha1 b hb hb1
        obtain ⟨k, hk⟩ := hg m hm
        have h1 : (g ^ j)⁻¹ * a * g ^ j = a := by rw [← hj a ha]; exact hna
        have h2 : (g ^ k)⁻¹ * a * g ^ k = b := by rw [← hk a ha]; exact hmab
        have hc : g ^ k * g ^ j = g ^ j * g ^ k := by rw [← pow_add, ← pow_add, add_comm]
        have key : ∀ X Y a : G, Y * X = X * Y →
            X⁻¹ * (Y⁻¹ * a * Y) * X = Y⁻¹ * (X⁻¹ * a * X) * Y := by
          intro X Y a h
          calc X⁻¹ * (Y⁻¹ * a * Y) * X = (Y * X)⁻¹ * a * (Y * X) := by group
            _ = (X * Y)⁻¹ * a * (X * Y) := by rw [h]
            _ = Y⁻¹ * (X⁻¹ * a * X) * Y := by group
        calc n⁻¹ * b * n = (g ^ j)⁻¹ * b * g ^ j := hj b hb
          _ = (g ^ j)⁻¹ * ((g ^ k)⁻¹ * a * g ^ k) * g ^ j := by rw [h2]
          _ = (g ^ k)⁻¹ * ((g ^ j)⁻¹ * a * g ^ j) * g ^ k := key _ _ _ hc
          _ = (g ^ k)⁻¹ * a * g ^ k := by rw [h1]
          _ = b := h2
    have hx' : x ∈ V ⊔ B := by rw [← hUVB]; exact hx
    obtain ⟨v, hv, b, hb, rfl⟩ := (ComponentSplitting.mem_sup_iff_of_commute hAB).1 hx'
    have hnb : n⁻¹ * b * n = b := by
      have := hBcomm n⁻¹ (L.inv_mem hn.1) b hb
      simpa using this
    calc n⁻¹ * (v * b) * n = (n⁻¹ * v * n) * (n⁻¹ * b * n) := by group
      _ = v * b := by rw [hnV v hv, hnb]
  · intro n hn
    obtain ⟨k, hk⟩ := hg n hn
    refine ⟨k, fun x hx => ?_⟩
    have hx' : x ∈ V ⊔ B := by rw [← hUVB]; exact hx
    obtain ⟨v, hv, b, hb, rfl⟩ := (ComponentSplitting.mem_sup_iff_of_commute hAB).1 hx'
    have hgk : g ^ k ∈ L := L.pow_mem hgN.1 k
    have hnb : n⁻¹ * b * n = b := by
      have := hBcomm n⁻¹ (L.inv_mem hn.1) b hb
      simpa using this
    have hgb : (g ^ k)⁻¹ * b * g ^ k = b := by
      have := hBcomm (g ^ k)⁻¹ (L.inv_mem hgk) b hb
      simpa using this
    calc n⁻¹ * (v * b) * n = (n⁻¹ * v * n) * (n⁻¹ * b * n) := by group
      _ = ((g ^ k)⁻¹ * v * g ^ k) * b := by rw [hk v hv, hnb]
      _ = ((g ^ k)⁻¹ * v * g ^ k) * ((g ^ k)⁻¹ * b * g ^ k) := by rw [hgb]
      _ = (g ^ k)⁻¹ * (v * b) * g ^ k := by group

end CFSG.QuasithinUnique
