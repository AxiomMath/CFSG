module

public import CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinPerp23R8Z6Defs
public import CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinPerp23R8ZOdd
public import CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinPerp23R8AAE7
public import CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinThinPf18CrossSetting
public import CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinThinPf18CrossModel
public import CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinPerpV3Pf93WO2
public import CFSG.ClassicalInvolution.Q3.Sec13End16M
public import CFSG.ClassicalInvolution.Q3.E64Ker.Main
public import CFSG.ClassicalInvolution.Sp62Rec.ModelCR1E64
public import CFSG.ClassicalInvolution.Solomon73.YamakiTables
public import Certificates.Kernel.ThCent.Leaves
public import CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinPerp23R8ZTwo
public import CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinThinComm
public import CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinThinE8
public import CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinThinPf10W
public import CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinThinPf11Vec
public import CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinThinPf4Thin
public import CFSG.ClassicalInvolution.Sp62Rec.ModelCR1

public section

set_option linter.unusedSectionVars false

namespace CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinPerp23

open CFSG CFSG.Open CFSG.ClassicalInvolution CFSG.ClassicalInvolution.Generic
  CFSG.ClassicalInvolution.Asc77 CFSG.ClassicalInvolution.Disconnected.AschTight
  CFSG.ClassicalInvolution.Q3 CFSG.ClassicalInvolution.Q3.PhilipHall.Frame
  CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinPerp
  CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinDisc CFSG.ClassicalInvolution.Uniform
  CFSG.ClassicalInvolution.Q3.Q3NL
  CFSG.ClassicalInvolution.Sp62Rec CFSG.ClassicalInvolution.Balance

section Leaves

@[expose] def P23E8ZXW (n : ℕ) : Prop :=
  CIT3Below n → TL4.TightBelowRPlus 3 n →
  ∀ (Y : Type) [Group Y] [Finite Y] (R : Subgroup Y) (S : Sylow 2 R) (t : Y) (K' W : Subgroup Y)
    (u e g : Y), P23Cfg n Y R S t K' W u e g → ¬ SecNoExit R e →
      u * e ∈ zStarOf (rLayer (Om R) u) → SecAE R e 6 →
        ∀ Z : Subgroup Y, I1In R t e Z →
          I1Six t e (rLayer (Om R) e) (Z ⊔ rLayer (Om R) e) →
          oddCoreIn (Subgroup.centralizer ({e} : Set Y)) = ⊥ →
          ∀ T A : Subgroup Y, T ≤ Z ⊔ rLayer (Om R) e → Nat.card T = 512 → A ≤ T →
            Solomon73.IsE64 A → (∀ A' ≤ T, Solomon73.IsE64 A' → A' = A) →
              ∃ x ∈ Subgroup.normalizer (A : Set Y), ∃ K ∈ Om R,
                K ≤ Subgroup.normalizer (A : Set Y) ∧ conjSub x K = K ∧
                  ∀ U : Subgroup Y, U ≤ K → IsCyclic U → Nat.card U = 4 → conjSub x U ≠ U

@[expose] def P23E8ZXE (n : ℕ) : Prop :=
  CIT3Below n → TL4.TightBelowRPlus 3 n →
  ∀ (Y : Type) [Group Y] [Finite Y] (R : Subgroup Y) (S : Sylow 2 R) (t : Y) (K' W : Subgroup Y)
    (u e g : Y), P23Cfg n Y R S t K' W u e g → ¬ SecNoExit R e →
      u * e ∈ zStarOf (rLayer (Om R) u) → SecAE R e 6 →
        ∀ Z : Subgroup Y, I1In R t e Z →
          I1Six t e (rLayer (Om R) e) (Z ⊔ rLayer (Om R) e) →
          oddCoreIn (Subgroup.centralizer ({e} : Set Y)) = ⊥ →
          ∀ T A : Subgroup Y, T ≤ Z ⊔ rLayer (Om R) e → Nat.card T = 512 → A ≤ T →
            Solomon73.IsE64 A → (∀ A' ≤ T, Solomon73.IsE64 A' → A' = A) →
              3 ≤ {J | J ∈ Om R ∧ J ≤ Subgroup.normalizer (A : Set Y) ∧
                  J ≤ Subgroup.centralizer ({e} : Set Y)}.ncard ∧
                {J | J ∈ Om R ∧ J ≤ Subgroup.normalizer (A : Set Y) ∧
                  J ≤ Subgroup.centralizer ({e} : Set Y)}.ncard ≤ 9

@[expose] def P23E8ZXStrong (n : ℕ) : Prop :=
  CIT3Below n → TL4.TightBelowRPlus 3 n →
  ∀ (Y : Type) [Group Y] [Finite Y] (R : Subgroup Y) (S : Sylow 2 R) (t : Y) (K' W : Subgroup Y)
    (u e g : Y), P23Cfg n Y R S t K' W u e g → ¬ SecNoExit R e →
      u * e ∈ zStarOf (rLayer (Om R) u) → SecAE R e 6 →
        ∀ Z : Subgroup Y, I1In R t e Z →
          I1Six t e (rLayer (Om R) e) (Z ⊔ rLayer (Om R) e) →
          oddCoreIn (Subgroup.centralizer ({e} : Set Y)) = ⊥ →
          ∀ T A : Subgroup Y, T ≤ Z ⊔ rLayer (Om R) e → Nat.card T = 512 → A ≤ T →
            Solomon73.IsE64 A → (∀ A' ≤ T, Solomon73.IsE64 A' → A' = A) →
              ∃ X : Subgroup Y, X ≤ Subgroup.normalizer (A : Set Y) ∧
                (∀ g ∈ Subgroup.normalizer (A : Set Y), X.map (MulAut.conj g).toMonoidHom = X) ∧
                ∃ ν : ↥X →* ↥Solomon73.Yamaki.N0, Function.Surjective ν ∧
                  Nat.card ν.ker ≤ 2 ∧ ν.ker ≤ Subgroup.center ↥X

end Leaves

namespace ZX

open CFSG.ClassicalInvolution.Q3.TC.Thin

section Gen

variable {G : Type} [Group G] [Finite G]

theorem isE64_conjSub {A : Subgroup G} (hA : Solomon73.IsE64 A) (g : G) :
    Solomon73.IsE64 (conjSub g A) := by
  obtain ⟨hab, hsq, hcard⟩ := hA
  refine ⟨?_, ?_, ?_⟩
  · intro a ha b hb
    rw [mem_conjSub_iff] at ha hb
    have := hab _ ha _ hb
    calc a * b = g * ((g⁻¹ * a * g) * (g⁻¹ * b * g)) * g⁻¹ := by group
      _ = g * ((g⁻¹ * b * g) * (g⁻¹ * a * g)) * g⁻¹ := by rw [this]
      _ = b * a := by group
  · intro a ha
    rw [mem_conjSub_iff] at ha
    have := hsq _ ha
    calc a * a = g * ((g⁻¹ * a * g) * (g⁻¹ * a * g)) * g⁻¹ := by group
      _ = 1 := by rw [this]; group
  · rw [← hcard]
    exact Subgroup.card_map_of_injective (MulAut.conj g).injective

theorem le_normalizer_of_unique {T A : Subgroup G} (hAT : A ≤ T) (hA : Solomon73.IsE64 A)
    (huniq : ∀ A' ≤ T, Solomon73.IsE64 A' → A' = A) :
    T ≤ Subgroup.normalizer (A : Set G) := by
  intro x hx
  have hle : conjSub x A ≤ T := by
    have := conjSub_mono (n := x) hAT
    rwa [conjSub_eq_self_of_mem hx] at this
  have heq : conjSub x A = A := huniq _ hle (isE64_conjSub hA x)
  rw [Subgroup.mem_normalizer_iff]
  intro y
  constructor
  · intro hy
    have : x * y * x⁻¹ ∈ conjSub x A := conj_mem_conjSub hy
    rwa [heq] at this
  · intro hy
    have : x * y * x⁻¹ ∈ conjSub x A := by rw [heq]; exact hy
    rw [mem_conjSub_iff] at this
    simpa [mul_assoc] using this

theorem mem_of_central {T A : Subgroup G} (hAT : A ≤ T) (hA : Solomon73.IsE64 A)
    (huniq : ∀ A' ≤ T, Solomon73.IsE64 A' → A' = A) {c : G} (hcT : c ∈ T) (hc2 : c * c = 1)
    (hcen : ∀ x ∈ T, c * x = x * c) : c ∈ A := by
  classical
  by_contra hcA
  obtain ⟨hab, hsq, hcard⟩ := hA
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨H₀, hH₀⟩ := Sylow.exists_subgroup_card_pow_prime 2 (n := 5) (G := ↥A)
    (by rw [hcard]; norm_num)
  set H : Subgroup G := H₀.map A.subtype with hH
  have hHA : H ≤ A := Subgroup.map_subtype_le _
  have hHcard : Nat.card H = 32 := by
    rw [hH, Subgroup.card_map_of_injective A.subtype_injective, hH₀]
    norm_num
  have hcinv : c⁻¹ = c := inv_eq_of_mul_eq_one_right hc2
  have hT' : ∀ x, c * x ∈ T → x ∈ T := fun x hx => by
    have := T.mul_mem (T.inv_mem hcT) hx
    rwa [inv_mul_cancel_left] at this
  let S : Subgroup G :=
    { carrier := {x | x ∈ H ∨ c * x ∈ H}
      one_mem' := Or.inl H.one_mem
      mul_mem' := by
        intro x y hx hy
        rcases hx with hx | hx <;> rcases hy with hy | hy
        · exact Or.inl (H.mul_mem hx hy)
        · right
          have : c * (x * y) = x * (c * y) := by
            rw [← mul_assoc, hcen x (hAT (hHA hx)), mul_assoc]
          rw [this]
          exact H.mul_mem hx hy
        · right
          rw [← mul_assoc]
          exact H.mul_mem hx hy
        · left
          have hxT : x ∈ T := hT' x (hAT (hHA hx))
          have : x * y = (c * x) * (c * y) := by
            rw [← (show Commute c x from hcen x hxT).mul_mul_mul_comm c y, hc2, one_mul]
          rw [this]
          exact H.mul_mem hx hy
      inv_mem' := by
        intro x hx
        rcases hx with hx | hx
        · exact Or.inl (H.inv_mem hx)
        · right
          have hxT : x ∈ T := hT' x (hAT (hHA hx))
          have : c * x⁻¹ = (c * x)⁻¹ := by
            rw [mul_inv_rev, hcinv]
            exact hcen _ (T.inv_mem hxT)
          rw [this]
          exact H.inv_mem hx }
  have hST : S ≤ T := by
    intro x hx
    rcases hx with hx | hx
    · exact hAT (hHA hx)
    · exact hT' x (hAT (hHA hx))
  have hcS : c ∈ S := Or.inr (by rw [hc2]; exact H.one_mem)
  have hC : ∀ a ∈ A, Commute c a := fun a ha => hcen a (hAT ha)
  have key : ∀ x ∈ S, ∃ a ∈ A, x = a ∨ x = c * a := by
    intro x hx
    rcases hx with hx | hx
    · exact ⟨x, hHA hx, Or.inl rfl⟩
    · refine ⟨c * x, hHA hx, Or.inr ?_⟩
      rw [← mul_assoc, hc2, one_mul]
  have hSab : ∀ x ∈ S, ∀ y ∈ S, x * y = y * x := by
    intro x hx y hy
    obtain ⟨a, ha, hxa⟩ := key x hx
    obtain ⟨b, hb, hyb⟩ := key y hy
    rcases hxa with hxa | hxa <;> rcases hyb with hyb | hyb <;> rw [hxa, hyb]
    · exact hab a ha b hb
    · exact (Commute.mul_right (hC a ha).symm (hab a ha b hb : Commute a b)).eq
    · exact (Commute.mul_left (hC b hb) (hab a ha b hb : Commute a b)).eq
    · exact (Commute.mul_right (Commute.mul_left (Commute.refl c) (hC a ha).symm)
        (Commute.mul_left (hC b hb) (hab a ha b hb : Commute a b))).eq
  have hSsq : ∀ x ∈ S, x * x = 1 := by
    intro x hx
    obtain ⟨a, ha, hxa⟩ := key x hx
    rcases hxa with hxa | hxa <;> rw [hxa]
    · exact hsq a ha
    · rw [(hC a ha).symm.mul_mul_mul_comm c a, hc2, one_mul]
      exact hsq a ha
  have hdisj : Disjoint (H : Set G) ((fun x => c⁻¹ * x) '' (H : Set G)) := by
    rw [Set.disjoint_left]
    rintro x hx ⟨y, hy, rfl⟩
    apply hcA
    have : c⁻¹ * y * y⁻¹ ∈ H := H.mul_mem hx (H.inv_mem hy)
    rw [mul_inv_cancel_right] at this
    rw [← hcinv]
    exact hHA this
  have hSset : (S : Set G) = (H : Set G) ∪ (fun x => c⁻¹ * x) '' (H : Set G) := by
    ext x
    constructor
    · rintro (hx | hx)
      · exact Or.inl hx
      · exact Or.inr ⟨c * x, hx, inv_mul_cancel_left c x⟩
    · rintro (hx | ⟨y, hy, rfl⟩)
      · exact Or.inl hx
      · right
        show c * (c⁻¹ * y) ∈ H
        rwa [← mul_assoc, mul_inv_cancel, one_mul]
  have hScard : Nat.card S = 64 := by
    have e1 : Nat.card S = (S : Set G).ncard := Nat.card_coe_set_eq _
    have e2 : Nat.card H = (H : Set G).ncard := Nat.card_coe_set_eq _
    rw [e1, hSset, Set.ncard_union_eq hdisj (Set.toFinite _) (Set.toFinite _),
      Set.ncard_image_of_injective _ (mul_right_injective c⁻¹), ← e2, hHcard]
  have hSA : S = A := huniq S hST ⟨hSab, hSsq, hScard⟩
  exact hcA (hSA ▸ hcS)

theorem isCyclic_of_card_four {K U : Subgroup G} {z : G} (hz : IsUniqueInvolution K z)
    (hUK : U ≤ K) (hU : Nat.card U = 4) : IsCyclic U := by
  by_contra hnc
  have hsq : ∀ u ∈ U, u * u = 1 := by
    intro u hu
    by_contra hne
    apply hnc
    have hdvd : orderOf (⟨u, hu⟩ : U) ∣ 4 := hU ▸ orderOf_dvd_natCard _
    have hpos : 0 < orderOf (⟨u, hu⟩ : U) := orderOf_pos _
    have hle : orderOf (⟨u, hu⟩ : U) ≤ 4 := Nat.le_of_dvd (by norm_num) hdvd
    have h2 : ¬ orderOf (⟨u, hu⟩ : U) ∣ 2 := by
      intro h
      apply hne
      have h1 := orderOf_dvd_iff_pow_eq_one.mp h
      have h1' := congrArg Subtype.val h1
      simpa [pow_two] using h1'
    have h4 : orderOf (⟨u, hu⟩ : U) = 4 := by
      interval_cases h : orderOf (⟨u, hu⟩ : U) <;> simp_all
    exact isCyclic_of_orderOf_eq_card _ (h4.trans hU.symm)
  have : Nat.card U ≤ 2 := natCard_subgroup_le_two_of_subset (a := 1) (b := z) fun u hu =>
    hz.unique u (hUK hu) (hsq u hu)
  omega

theorem comm_of_phi_comm {M : Type} [Group M] {Δ P : Set (Subgroup G)} (hΩ : HypOmegaGen Δ)
    (h2 : ∀ L ∈ Δ, IsPGroup 2 L) (hPΔ : P ⊆ Δ) (φ : ↥(pSpan P) →* M) (hk : IsPGroup 2 φ.ker)
    {L₁ L₂ : Subgroup G} (h₁ : L₁ ∈ P) (h₂ : L₂ ∈ P) (hne : L₁ ≠ L₂)
    (hc : ∀ x ∈ (L₁.subgroupOf (pSpan P)).map φ, ∀ y ∈ (L₂.subgroupOf (pSpan P)).map φ,
      x * y = y * x) :
    ∀ x ∈ L₁, ∀ y ∈ L₂, x * y = y * x := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hm : ∀ {L : Subgroup G}, L ∈ P → IsPGroup 2 ((L.subgroupOf (pSpan P)).map φ) :=
    fun hL => ((h2 _ (hPΔ hL)).of_equiv (Subgroup.subgroupOfEquivOfLe (le_pSpan hL)).symm).map _
  have hN : (L₁.subgroupOf (pSpan P)).map φ ≤
      Subgroup.normalizer ((L₂.subgroupOf (pSpan P)).map φ : Set M) :=
    le_normalizer_of_comm hc
  set S := (L₁.subgroupOf (pSpan P)).map φ ⊔ (L₂.subgroupOf (pSpan P)).map φ with hSdef
  have hS2 : IsPGroup 2 ↥S := (hm h₁).to_sup_of_normal_right' (hm h₂) hN
  have hQ2 : IsPGroup 2 ((S.comap φ).map (pSpan P).subtype) :=
    (hS2.comap_of_ker_isPGroup φ hk).map _
  have hLQ : ∀ {L : Subgroup G}, L ∈ P → (L.subgroupOf (pSpan P)).map φ ≤ S →
      L ≤ (S.comap φ).map (pSpan P).subtype := by
    intro L hL hLS l hl
    exact ⟨⟨l, le_pSpan hL hl⟩, hLS ⟨⟨l, le_pSpan hL hl⟩, Subgroup.mem_subgroupOf.mpr hl, rfl⟩,
      rfl⟩
  exact TL4.commutes_of_le_two hΩ h2 (hPΔ h₁) (hPΔ h₂) hne hQ2 (hLQ h₁ le_sup_left)
    (hLQ h₂ le_sup_right)

end Gen

section Fam

variable {Y : Type} [Group Y]

abbrev famA (R A : Subgroup Y) : Set (Subgroup Y) :=
  {J | J ∈ Om R ∧ J ≤ Subgroup.normalizer (A : Set Y)}

abbrev xA (R A : Subgroup Y) : Subgroup Y := TC.Thin.pSpan (famA R A)

theorem conjSub_le_normalizer {J L : Subgroup Y} (h : J ≤ Subgroup.normalizer (L : Set Y))
    (x : Y) : conjSub x J ≤ Subgroup.normalizer (conjSub x L : Set Y) := by
  intro y hy
  rw [mem_conjSub_iff] at hy
  have h1 := Subgroup.mem_normalizer_iff.mp (h hy)
  rw [Subgroup.mem_normalizer_iff]
  intro w
  rw [mem_conjSub_iff, mem_conjSub_iff]
  have e : x⁻¹ * (y * w * y⁻¹) * x =
      (x⁻¹ * y * x) * (x⁻¹ * w * x) * (x⁻¹ * y * x)⁻¹ := by group
  rw [e]
  exact h1 _

theorem conjSub_mem_famA {R A : Subgroup Y} {x : Y} (hx : x ∈ Subgroup.normalizer (A : Set Y))
    {L : Subgroup Y} (hL : L ∈ famA R A) : conjSub x L ∈ famA R A := by
  refine ⟨conjInvariant_conjClass (tightCore R) x L hL.1, ?_⟩
  have h1 := conjSub_mono (n := x) hL.2
  rwa [conjSub_eq_self_of_mem hx] at h1

theorem xA_le (R A : Subgroup Y) : xA R A ≤ Subgroup.normalizer (A : Set Y) :=
  TC.Thin.pSpan_le fun _ hL => hL.2

theorem mem_normalizer_xA {R A : Subgroup Y} {x : Y} (hx : x ∈ Subgroup.normalizer (A : Set Y)) :
    x ∈ Subgroup.normalizer ((xA R A : Subgroup Y) : Set Y) :=
  TC.Thin.mem_normalizer_pSpan (fun _ hL => conjSub_mem_famA hx hL)
    (fun _ hL => conjSub_mem_famA (inv_mem hx) hL)

theorem conjSub_eq_of_normalizer {K : Subgroup Y} {y : Y}
    (hy : y ∈ Subgroup.normalizer (K : Set Y)) : conjSub y K = K := by
  ext x
  rw [mem_conjSub_iff]
  constructor
  · intro h
    have := (Subgroup.mem_normalizer_iff.mp hy _).mp h
    simpa [mul_assoc] using this
  · intro h
    apply (Subgroup.mem_normalizer_iff.mp hy _).mpr
    simpa [mul_assoc] using h

theorem conjSub_xA {R A : Subgroup Y} {x : Y} (hx : x ∈ Subgroup.normalizer (A : Set Y)) :
    conjSub x (xA R A) = xA R A :=
  conjSub_eq_of_normalizer (mem_normalizer_xA hx)

theorem le_xA_iff {R A J : Subgroup Y} (hJ : J ∈ Om R) :
    J ≤ xA R A ↔ J ≤ Subgroup.normalizer (A : Set Y) :=
  ⟨fun h => h.trans (xA_le R A), fun h => TC.Thin.le_pSpan ⟨hJ, h⟩⟩

theorem le_normalizer_of_subgroupOf {X J L : Subgroup Y} (hJX : J ≤ X) (hLX : L ≤ X)
    (h : J.subgroupOf X ≤ Subgroup.normalizer ((L.subgroupOf X : Subgroup X) : Set X)) :
    J ≤ Subgroup.normalizer (L : Set Y) := by
  intro j hj
  have hj' := Subgroup.mem_normalizer_iff.mp
    (h (show (⟨j, hJX hj⟩ : X) ∈ J.subgroupOf X from Subgroup.mem_subgroupOf.mpr hj))
  rw [Subgroup.mem_normalizer_iff]
  intro y
  by_cases hy : y ∈ X
  · have := hj' ⟨y, hy⟩
    simpa only [Subgroup.mem_subgroupOf, Subgroup.coe_mul, Subgroup.coe_inv] using this
  · constructor
    · intro hyL
      exact absurd (hLX hyL) hy
    · intro hyL
      exfalso
      apply hy
      have e : y = j⁻¹ * (j * y * j⁻¹) * j := by group
      rw [e]
      exact X.mul_mem (X.mul_mem (X.inv_mem (hJX hj)) (hLX hyL)) (hJX hj)

end Fam

section Aut

variable {Y : Type} [Group Y] [Finite Y]

@[expose] def conjX (X : Subgroup Y) {x : Y} (hx : x ∈ Subgroup.normalizer (X : Set Y)) :
    ↥X ≃* ↥X where
  toFun y := ⟨x * y * x⁻¹, (Subgroup.mem_normalizer_iff.mp hx y).mp y.2⟩
  invFun y := ⟨x⁻¹ * y * x, by
    have := (Subgroup.mem_normalizer_iff.mp (inv_mem hx) y).mp y.2
    simpa using this⟩
  left_inv y := Subtype.ext (by simp [mul_assoc])
  right_inv y := Subtype.ext (by simp [mul_assoc])
  map_mul' a b := Subtype.ext (by simp [mul_assoc])

theorem conjX_apply (X : Subgroup Y) {x : Y} (hx : x ∈ Subgroup.normalizer (X : Set Y))
    (y : ↥X) : ((conjX X hx y : ↥X) : Y) = x * y * x⁻¹ := rfl

theorem conjX_symm_apply (X : Subgroup Y) {x : Y} (hx : x ∈ Subgroup.normalizer (X : Set Y))
    (y : ↥X) : (((conjX X hx).symm y : ↥X) : Y) = x⁻¹ * y * x⁻¹⁻¹ := by
  rw [inv_inv]
  rfl

@[expose] noncomputable def secAutX (X : Subgroup Y) {x : Y}
    (hx : x ∈ Subgroup.normalizer (X : Set Y)) : SecQuot X ≃* SecQuot X :=
  QuotientGroup.congr _ _ (conjX X hx) (TwinPerpV3.classicalInvolutionOddCore_map_equiv _)

theorem secAutX_mk (X : Subgroup Y) {x : Y} (hx : x ∈ Subgroup.normalizer (X : Set Y))
    (y : ↥X) :
    secAutX X hx (QuotientGroup.mk' (classicalInvolutionOddCore ↥X) y) =
      QuotientGroup.mk' (classicalInvolutionOddCore ↥X) (conjX X hx y) := rfl

theorem map_congr_secImage {X : Subgroup Y} (e : ↥X ≃* ↥X)
    (he : (classicalInvolutionOddCore ↥X).map (e : ↥X →* ↥X) = classicalInvolutionOddCore ↥X)
    {c : Y} (hc : ∀ y : ↥X, ((e y : ↥X) : Y) = c * y * c⁻¹) (J : Subgroup Y) :
    (secImage X J).map (QuotientGroup.congr _ _ e he).toMonoidHom = secImage X (conjSub c J) := by
  ext q
  constructor
  · rintro ⟨_, ⟨y, hy, rfl⟩, rfl⟩
    refine ⟨e y, Subgroup.mem_subgroupOf.mpr ?_, rfl⟩
    rw [hc, mem_conjSub_iff]
    have hy' : (y : Y) ∈ J := Subgroup.mem_subgroupOf.mp hy
    simpa [mul_assoc] using hy'
  · rintro ⟨y, hy, rfl⟩
    refine ⟨QuotientGroup.mk' _ (e.symm y), ⟨e.symm y, Subgroup.mem_subgroupOf.mpr ?_, rfl⟩, ?_⟩
    · have h1 : ((e (e.symm y) : ↥X) : Y) = c * (e.symm y : Y) * c⁻¹ := hc _
      rw [MulEquiv.apply_symm_apply] at h1
      have hy' : c⁻¹ * (y : Y) * c ∈ J := mem_conjSub_iff.mp (Subgroup.mem_subgroupOf.mp hy)
      have e2 : ((e.symm y : ↥X) : Y) = c⁻¹ * (y : Y) * c := by
        rw [h1]
        group
      rw [e2]
      exact hy'
    · show QuotientGroup.congr _ _ e he (QuotientGroup.mk' _ (e.symm y)) = QuotientGroup.mk' _ y
      rw [QuotientGroup.congr_mk', MulEquiv.apply_symm_apply]

theorem map_secAutX_secImage (X : Subgroup Y) {x : Y}
    (hx : x ∈ Subgroup.normalizer (X : Set Y)) (J : Subgroup Y) :
    (secImage X J).map (secAutX X hx).toMonoidHom = secImage X (conjSub x J) :=
  map_congr_secImage (conjX X hx) _ (conjX_apply X hx) J

theorem map_secAutX_symm_secImage (X : Subgroup Y) {x : Y}
    (hx : x ∈ Subgroup.normalizer (X : Set Y)) (J : Subgroup Y) :
    (secImage X J).map (secAutX X hx).symm.toMonoidHom = secImage X (conjSub x⁻¹ J) :=
  map_congr_secImage (conjX X hx).symm (TwinPerpV3.classicalInvolutionOddCore_map_equiv _)
    (conjX_symm_apply X hx) J

end Aut

section AutAE

open CFSG.ClassicalInvolution.Q3.AE

variable {G : Type} [Group G] [Finite G]

theorem exists_wr_of_aut {Φ : Set (Subgroup G)} {m : ℕ}
    (hm : 5 ≤ m) (hgen : pSpan Φ = ⊤) (I : AEIdent Φ m) (σ : G ≃* G)
    (hσ : ∀ L ∈ Φ, L.map σ.toMonoidHom ∈ Φ) :
    ∃ w : Wr m, ∀ x y : ↥(pSpan Φ), (y : G) = σ x →
      I.φ y = mkQ m w * I.φ x * (mkQ m w)⁻¹ := by
  have hmem : ∀ g : G, g ∈ pSpan Φ := fun g => by rw [hgen]; exact Subgroup.mem_top g
  let σ' : ↥(pSpan Φ) ≃* ↥(pSpan Φ) :=
    { toFun := fun x => ⟨σ x, hmem _⟩
      invFun := fun x => ⟨σ.symm x, hmem _⟩
      left_inv := fun x => Subtype.ext (by simp)
      right_inv := fun x => Subtype.ext (by simp)
      map_mul' := fun x y => Subtype.ext (by simp) }
  have hσ' : ∀ x : ↥(pSpan Φ), ((σ' x : ↥(pSpan Φ)) : G) = σ x := fun _ => rfl
  have hZ : Subgroup.center ↥I.φ.range = ⊥ :=
    TwinThin.center_eq_bot_of_eq I.range_eq (TwinThin.center_Hn hm)
  have hker : I.φ.ker = Subgroup.center ↥(pSpan Φ) := le_antisymm I.ker_le (I.center_le_ker hm)
  have hkσ : ∀ x : ↥(pSpan Φ), x ∈ I.φ.ker → σ' x ∈ I.φ.ker := by
    intro x hx
    rw [hker] at hx ⊢
    rw [Subgroup.mem_center_iff] at hx ⊢
    intro g
    have := hx (σ'.symm g)
    have h2 := congrArg σ' this
    simpa using h2
  let f : ↥(pSpan Φ) →* ↥I.φ.range := I.φ.rangeRestrict.comp σ'.toMonoidHom
  let σ'' : ↥I.φ.range →* ↥I.φ.range :=
    MonoidHom.liftOfRightInverse I.φ.rangeRestrict (Function.surjInv I.φ.rangeRestrict_surjective)
      (Function.rightInverse_surjInv _)
      ⟨f, fun x hx => by
        have hxk : x ∈ I.φ.ker := by
          rw [← MonoidHom.ker_rangeRestrict]
          exact hx
        rw [MonoidHom.mem_ker]
        apply Subtype.ext
        have := hkσ x hxk
        rw [MonoidHom.mem_ker] at this
        simpa [f] using this⟩
  have hσ''app : ∀ x : ↥(pSpan Φ), σ'' (I.φ.rangeRestrict x) = I.φ.rangeRestrict (σ' x) :=
    fun x => MonoidHom.liftOfRightInverse_comp_apply _ _ _ _ x
  have hsurj : Function.Surjective σ'' := by
    intro r
    obtain ⟨x, rfl⟩ := I.φ.rangeRestrict_surjective r
    exact ⟨I.φ.rangeRestrict (σ'.symm x), by rw [hσ''app]; simp⟩
  have hbij : Function.Bijective σ'' := ⟨Finite.injective_iff_surjective.mpr hsurj, hsurj⟩
  have hperm : TwinThinPf8.PermMembers I.φ.range σ'' := by
    intro β hβ cb
    obtain ⟨L, hL, hLlab⟩ := I.label_surj β hβ cb
    obtain ⟨β', hβ', cb', hlab'⟩ := I.label _ (hσ L hL)
    refine ⟨β', hβ', cb', fun x hx => ?_⟩
    have hx' : (x : AEQ m) ∈ (L.subgroupOf (pSpan Φ)).map I.φ := by rw [hLlab]; exact hx
    obtain ⟨l, hl, hlx⟩ := I.exists_of_mem_map hL hx'
    have hxe : x = I.φ.rangeRestrict ⟨l, le_pSpan hL hl⟩ := Subtype.ext hlx.symm
    rw [hxe, hσ''app, ← hlab']
    exact ⟨σ' ⟨l, le_pSpan hL hl⟩, Subgroup.mem_subgroupOf.mpr ⟨l, hl, rfl⟩, rfl⟩
  obtain ⟨w, hw⟩ := TwinThin.Cross.aeAut_of_five_le hm I.φ.range I.range_eq σ'' hbij hperm
  refine ⟨w, fun x y hxy => ?_⟩
  have h1 := hw (I.φ.rangeRestrict x)
  rw [hσ''app] at h1
  have hy : σ' x = y := Subtype.ext hxy.symm
  rw [hy] at h1
  exact h1

theorem card_const_sets {m : ℕ} (v : Fin m → ZMod 2) :
    ((Finset.univ.powersetCard 4 : Finset (Finset (Fin m))).filter
        (fun α => ∀ i ∈ α, ∀ j ∈ α, v i = v j)).card =
      (Finset.univ.filter (fun i => v i = 1)).card.choose 4 +
        (Finset.univ.filter (fun i => v i = 1))ᶜ.card.choose 4 := by
  classical
  set S : Finset (Fin m) := Finset.univ.filter (fun i => v i = 1) with hS
  have h01 : ∀ x : ZMod 2, x = 0 ∨ x = 1 := by decide
  have heq : (Finset.univ.powersetCard 4 : Finset (Finset (Fin m))).filter
      (fun α => ∀ i ∈ α, ∀ j ∈ α, v i = v j) = S.powersetCard 4 ∪ Sᶜ.powersetCard 4 := by
    ext α
    simp only [Finset.mem_filter, Finset.mem_powersetCard, Finset.mem_union, Finset.subset_univ,
      true_and]
    constructor
    · rintro ⟨hα, hc⟩
      obtain ⟨i₀, hi₀⟩ : α.Nonempty := Finset.card_pos.mp (by omega)
      rcases h01 (v i₀) with h | h
      · right
        refine ⟨fun i hi => ?_, hα⟩
        rw [Finset.mem_compl, hS, Finset.mem_filter]
        rintro ⟨-, h1⟩
        rw [hc i hi i₀ hi₀, h] at h1
        exact absurd h1 (by decide)
      · left
        refine ⟨fun i hi => ?_, hα⟩
        rw [hS, Finset.mem_filter]
        exact ⟨Finset.mem_univ _, (hc i hi i₀ hi₀).trans h⟩
    · rintro (⟨hαS, hα⟩ | ⟨hαS, hα⟩)
      · refine ⟨hα, fun i hi j hj => ?_⟩
        have h1 := (Finset.mem_filter.mp (hαS hi)).2
        have h2 := (Finset.mem_filter.mp (hαS hj)).2
        rw [h1, h2]
      · refine ⟨hα, fun i hi j hj => ?_⟩
        have h1 : ¬ v i = 1 := fun h => Finset.mem_compl.mp (hαS hi) (Finset.mem_filter.mpr
          ⟨Finset.mem_univ _, h⟩)
        have h2 : ¬ v j = 1 := fun h => Finset.mem_compl.mp (hαS hj) (Finset.mem_filter.mpr
          ⟨Finset.mem_univ _, h⟩)
        rw [(h01 (v i)).resolve_right h1, (h01 (v j)).resolve_right h2]
  have hdisj : Disjoint (S.powersetCard 4) (Sᶜ.powersetCard 4) := by
    rw [Finset.disjoint_left]
    intro α h1 h2
    rw [Finset.mem_powersetCard] at h1 h2
    obtain ⟨i, hi⟩ : α.Nonempty := Finset.card_pos.mp (by omega)
    exact Finset.mem_compl.mp (h2.1 hi) (h1.1 hi)
  rw [heq, Finset.card_union_of_disjoint hdisj, Finset.card_powersetCard,
    Finset.card_powersetCard]

theorem count_not_mem {m k : ℕ} (hm5 : 5 ≤ m) (hm7 : m ≤ 7) (hk : k ≤ m) :
    k.choose 4 + (m - k).choose 4 < 2 ∨ 5 ≤ k.choose 4 + (m - k).choose 4 := by
  interval_cases m <;> interval_cases k <;> decide

end AutAE

section OddE64

open CFSG.ClassicalInvolution.Q3.AE

variable {G : Type} [Group G] [Finite G]

theorem eq_one_of_central_commutator {p : ℕ} [hp : Fact p.Prime] (P : Sylow p G)
    (hPab : ∀ a ∈ (P : Subgroup G), ∀ b ∈ (P : Subgroup G), a * b = b * a) {z : G}
    (hz : z ∈ Subgroup.center G) (hzP : z ∈ (P : Subgroup G)) (hzc : z ∈ commutator G) :
    z = 1 := by
  have hkey : ∀ (k : ℕ) (g₀ : G), g₀⁻¹ * z ^ k * g₀ ∈ (P : Subgroup G) →
      g₀⁻¹ * z ^ k * g₀ = z ^ k := by
    intro k g₀ _
    rw [mul_assoc, ← Subgroup.mem_center_iff.mp (Subgroup.pow_mem _ hz k) g₀, ← mul_assoc,
      inv_mul_cancel, one_mul]
  let ϕ : (P : Subgroup G) →* Abelianization (P : Subgroup G) := Abelianization.of
  have h1 : ϕ.transfer z = 1 :=
    MonoidHom.mem_ker.mp (Abelianization.commutator_subset_ker ϕ.transfer hzc)
  rw [MonoidHom.transfer_eq_pow ϕ z hkey] at h1
  have h2 := MonoidHom.mem_ker.mpr h1
  rw [Abelianization.ker_of] at h2
  have hcomm : commutator (P : Subgroup G) = ⊥ := by
    rw [commutator_def, Subgroup.commutator_eq_bot_iff_le_centralizer]
    intro a _ b _
    exact Subtype.ext (hPab _ b.2 _ a.2)
  rw [hcomm, Subgroup.mem_bot] at h2
  have h3 : z ^ (P : Subgroup G).index = 1 := congrArg Subtype.val h2
  obtain ⟨k, hk⟩ := IsPGroup.iff_orderOf.mp P.isPGroup' ⟨z, hzP⟩
  rw [Subgroup.orderOf_mk] at hk
  have hcop : Nat.Coprime (orderOf z) (P : Subgroup G).index := by
    rw [hk]
    exact Nat.Coprime.pow_left k ((Nat.Prime.coprime_iff_not_dvd hp.out).mpr P.not_dvd_index)
  exact orderOf_eq_one_iff.mp (Nat.eq_one_of_dvd_coprimes hcop dvd_rfl
    (orderOf_dvd_of_pow_eq_one h3))

theorem oddCore_le_commutator {P : Set (Subgroup G)} (hP2 : ∀ L ∈ P, IsPGroup 2 L)
    (hgen : pSpan P = ⊤) : classicalInvolutionOddCore G ≤ commutator G := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hab : ∀ x : Abelianization G, x ∈ CommGroup.primaryComponent (Abelianization G) 2 := by
    intro x
    have htop : (pSpan P).map (Abelianization.of : G →* Abelianization G) ≤
        CommGroup.primaryComponent (Abelianization G) 2 := by
      rw [Subgroup.map_le_iff_le_comap]
      refine pSpan_le fun L hL l hl => ?_
      obtain ⟨k, hk⟩ := OddQuot.two_elt (hP2 L hL) hl
      exact CommGroup.mem_primaryComponent.mpr ⟨k, by rw [← map_pow, hk, map_one]⟩
    obtain ⟨g, rfl⟩ := QuotientGroup.mk_surjective (s := commutator G) x
    exact htop ⟨g, by rw [hgen]; exact Subgroup.mem_top g, rfl⟩
  intro z hz
  rw [← Abelianization.ker_of, MonoidHom.mem_ker]
  obtain ⟨k, hk⟩ := CommGroup.mem_primaryComponent.mp (hab (Abelianization.of z))
  have hodd : Odd (orderOf (Abelianization.of z)) := by
    refine Odd.of_dvd_nat ?_ (orderOf_map_dvd _ z)
    have := orderOf_dvd_natCard (⟨z, hz⟩ : classicalInvolutionOddCore G)
    rw [Subgroup.orderOf_mk] at this
    exact (CFSG.ComponentClassification.OddCore.odd_card G).of_dvd_nat this
  have hco : Nat.Coprime (2 ^ k) (orderOf (Abelianization.of z)) :=
    Nat.Coprime.pow_left k (Nat.coprime_two_left.mpr hodd)
  exact orderOf_eq_one_iff.mp (Nat.eq_one_of_dvd_coprimes hco
    (orderOf_dvd_of_pow_eq_one hk) dvd_rfl)

theorem sylow_comm_of_e64 (φ : G →* AEQ 7)
    (hφ : φ.range = e64Sub) (hker : φ.ker ≤ Subgroup.center G) {p : ℕ} [hp : Fact p.Prime]
    (hp2 : p ≠ 2) (P : Sylow p G) :
    ∀ a ∈ (P : Subgroup G), ∀ b ∈ (P : Subgroup G), a * b = b * a := by
  set Pφ : Subgroup (AEQ 7) := (P : Subgroup G).map φ with hPφ
  have hrange : Pφ ≤ e64Sub := by
    rw [← hφ]
    rintro _ ⟨x, -, rfl⟩
    exact ⟨x, rfl⟩
  have he64 : Nat.card e64Sub = 10752 :=
    le_antisymm Sp62Rec.card_e64Sub_le E64Ker.le_card_e64Sub
  have hdvd : Nat.card Pφ ∣ 10752 := he64 ▸ Subgroup.card_dvd_of_le hrange
  have hpg : IsPGroup p Pφ := P.isPGroup'.map φ
  obtain ⟨k, hk⟩ := IsPGroup.iff_card.mp hpg
  have hk1 : k ≤ 1 := by
    by_contra hk1
    have h2 : p ^ 2 ∣ 2 ^ 9 * 21 := (pow_dvd_pow p (by omega)).trans (hk ▸ hdvd)
    have hcop : Nat.Coprime (p ^ 2) (2 ^ 9) :=
      Nat.Coprime.pow 2 9 ((Nat.coprime_primes hp.out Nat.prime_two).mpr hp2)
    have h3 : p ^ 2 ∣ 21 := hcop.dvd_of_dvd_mul_left (by rwa [mul_comm] at h2)
    have h4 : p ^ 2 ≤ 21 := Nat.le_of_dvd (by norm_num) h3
    have h5 : p ≤ 4 := by nlinarith
    have h6 := hp.out.two_le
    rcases (by omega : p = 3 ∨ p = 4) with h | h <;> rw [h] at h3 <;> norm_num at h3
  have hcyc : IsCyclic Pφ := by
    interval_cases k
    · rw [pow_zero] at hk
      have : Subsingleton Pφ := (Nat.card_eq_one_iff_unique.mp hk).1
      exact isCyclic_of_subsingleton
    · rw [pow_one] at hk
      exact isCyclic_of_prime_card hk
  set f : ↥(P : Subgroup G) →* ↥Pφ := (φ.comp (P : Subgroup G).subtype).codRestrict Pφ
    (fun x => ⟨x, x.2, rfl⟩) with hf
  have hkf : f.ker ≤ Subgroup.center (P : Subgroup G) := by
    intro x hx
    have hxk : (x : G) ∈ φ.ker := by
      rw [MonoidHom.mem_ker]
      exact congrArg Subtype.val (MonoidHom.mem_ker.mp hx)
    rw [Subgroup.mem_center_iff]
    intro y
    exact Subtype.ext (Subgroup.mem_center_iff.mp (hker hxk) y)
  intro a ha b hb
  have := commutative_of_cyclic_center_quotient f hkf ⟨a, ha⟩ ⟨b, hb⟩
  exact congrArg Subtype.val this

theorem oddCore_eq_bot_of_e64 {P : Set (Subgroup G)}
    (hP2 : ∀ L ∈ P, IsPGroup 2 L) (hgen : pSpan P = ⊤)
    (hc : classicalInvolutionOddCore G ≤ Subgroup.center G) (φ : G →* AEQ 7)
    (hφ : φ.range = e64Sub) (hker : φ.ker ≤ Subgroup.center G) :
    classicalInvolutionOddCore G = ⊥ := by
  by_contra hne
  have hodd := CFSG.ComponentClassification.OddCore.odd_card G
  have hcard : Nat.card (classicalInvolutionOddCore G) ≠ 1 := fun h =>
    hne (Subgroup.eq_bot_of_card_eq _ h)
  obtain ⟨p, hp, hpd⟩ := Nat.exists_prime_and_dvd hcard
  have : Fact p.Prime := ⟨hp⟩
  have hp2 : p ≠ 2 := by
    rintro rfl
    exact (Nat.not_even_iff_odd.mpr hodd) (even_iff_two_dvd.mpr hpd)
  obtain ⟨⟨z, hzN⟩, hz⟩ := exists_prime_orderOf_dvd_card' p hpd
  rw [Subgroup.orderOf_mk] at hz
  have hz2 : IsPGroup p (Subgroup.zpowers z) := IsPGroup.of_card (n := 1)
    (by rw [Nat.card_zpowers, hz, pow_one])
  obtain ⟨Q, hQ⟩ := hz2.exists_le_sylow
  have h1 := eq_one_of_central_commutator Q (sylow_comm_of_e64 φ hφ hker hp2 Q) (hc hzN)
    (hQ (Subgroup.mem_zpowers z)) (oddCore_le_commutator hP2 hgen hzN)
  rw [h1, orderOf_one] at hz
  exact hp.one_lt.ne hz

end OddE64

section Cert

variable {n : ℕ} {Y : Type} [Group Y] [Finite Y] {R : Subgroup Y} {S : Sylow 2 R} {t : Y}
  {K' W : Subgroup Y} {u e g : Y} {A : Subgroup Y} {b : Y}

structure Hyp (n : ℕ) (Y : Type) [Group Y] [Finite Y] (R : Subgroup Y) (S : Sylow 2 R) (t : Y)
    (K' W : Subgroup Y) (u e g : Y) (A : Subgroup Y) (b : Y) : Prop where
  cfg : P23Cfg n Y R S t K' W u e g
  two : ∀ J ∈ Om R, IsPGroup 2 J
  e64 : Solomon73.IsE64 A
  K_le : conjSub b (tightCore R) ≤ Subgroup.normalizer (A : Set Y)
  K'_le : conjSub b K' ≤ Subgroup.normalizer (A : Set Y)
  tA : b * t * b⁻¹ ∈ A
  eA : e ∈ A
  bC : b ∈ Subgroup.centralizer ({e} : Set Y)
  w : ∃ x ∈ Subgroup.normalizer (A : Set Y), ∃ K ∈ Om R,
    K ≤ Subgroup.normalizer (A : Set Y) ∧ conjSub x K = K ∧
      ∀ U : Subgroup Y, U ≤ K → IsCyclic U → Nat.card U = 4 → conjSub x U ≠ U
  cnt : 3 ≤ {J | J ∈ Om R ∧ J ≤ Subgroup.normalizer (A : Set Y) ∧
      J ≤ Subgroup.centralizer ({e} : Set Y)}.ncard ∧
    {J | J ∈ Om R ∧ J ≤ Subgroup.normalizer (A : Set Y) ∧
      J ≤ Subgroup.centralizer ({e} : Set Y)}.ncard ≤ 9

namespace Hyp

variable (H : Hyp n Y R S t K' W u e g A b)
include H

theorem hypOmega : HypOmegaGen (Om R) := (CoreData.of_S H.cfg.std.perp.core).hyp

omit H in
theorem mem_K : tightCore R ∈ Om R := CoreAssembly.mem_conjClass_self _

theorem mem_K' : K' ∈ Om R := H.cfg.std.hK'.1

theorem isUniqueInvolution_t : IsUniqueInvolution (tightCore R) t :=
  Inner.isUniqueInvolution_core (CoreData.of_S H.cfg.std.perp.core).datum

theorem isUniqueInvolution_t' : IsUniqueInvolution K' t :=
  isUniqueInvolution_of_mem_twinSet H.isUniqueInvolution_t H.cfg.std.hK'

theorem aEmpty {L : Subgroup Y} (hL : L ∈ Om R) : AEmpty (Om R) L :=
  (CoreData.of_S H.cfg.std.perp.core).aEmpty_all L hL

theorem q8_of_mem {J : Subgroup Y} (hJ : J ∈ Om R) : Nonempty (↥J ≃* QuaternionGroup 2) :=
  members_sylow_q8 H.cfg.std.perp J hJ J
    ⟨le_rfl, H.two J hJ, fun _ hV' _ hle => le_antisymm hV' hle⟩

theorem card_of_mem {J : Subgroup Y} (hJ : J ∈ Om R) : Nat.card J = 8 := by
  obtain ⟨e8⟩ := H.q8_of_mem hJ
  rw [Nat.card_congr e8.toEquiv, Nat.card_eq_fintype_card, QuaternionGroup.card]

theorem perp_conj (x : Y) {J : Subgroup Y} (hJ : J ∈ Om R)
    (hJN : J ≤ Subgroup.normalizer (conjSub x (tightCore R) : Set Y)) :
    J = conjSub x (tightCore R) ∨ J = conjSub x K' := by
  have hperp : KPerp (Om R) (tightCore R) = {tightCore R, K'} :=
    H.cfg.std.perp.perp.trans (twinSet_eq_pair H.cfg.std.two H.cfg.std.hK' H.cfg.std.hne)
  set J₀ := conjSub x⁻¹ J with hJ₀
  have hJ₀Ω : J₀ ∈ Om R := H.hypOmega.conjInvariant _ _ hJ
  have hJ₀N : J₀ ≤ Subgroup.normalizer (tightCore R : Set Y) := by
    have := conjSub_le_normalizer hJN x⁻¹
    rwa [conjSub_inv_conjSub] at this
  have hJeq : J = conjSub x J₀ := by rw [hJ₀, conjSub_conjSub_inv]
  by_cases hne : J₀ = tightCore R
  · left
    rw [hJeq, hne]
  · have hn : J₀ ∈ omegaNbr (Om R) (tightCore R) :=
      (TC.mem_omegaNbr_iff H.hypOmega H.two).mpr ⟨hJ₀Ω, hne, hJ₀N⟩
    have hp : J₀ ∈ KPerp (Om R) (tightCore R) := Set.mem_insert_of_mem _ hn
    rw [hperp] at hp
    rcases hp with h | h
    · exact absurd h hne
    · right
      rw [hJeq, h]

theorem swap : ∃ y : Y, conjSub y (tightCore R) = K' ∧ conjSub y K' = tightCore R := by
  obtain ⟨y, hy⟩ := H.mem_K'
  replace hy : conjSub y (tightCore R) = K' := hy
  refine ⟨y, hy, ?_⟩
  have hyt : y * t * y⁻¹ = t := by
    have h1 := H.isUniqueInvolution_t.conj y
    rw [hy] at h1
    exact h1.eq H.isUniqueInvolution_t'
  have hiu : IsUniqueInvolution (conjSub y K') t := by
    have := H.isUniqueInvolution_t'.conj y
    rwa [hyt] at this
  have hmem : conjSub y K' ∈ twinSet (Om R) (tightCore R) :=
    ⟨H.hypOmega.conjInvariant _ _ H.mem_K', t, H.isUniqueInvolution_t, hiu⟩
  rw [twinSet_eq_pair H.cfg.std.two H.cfg.std.hK' H.cfg.std.hne] at hmem
  rcases hmem with h | h
  · exact h
  · exfalso
    apply H.cfg.std.hne
    have h2 : conjSub y K' = conjSub y (tightCore R) := by rw [h, hy]
    exact conjSub_injective y h2

theorem perp_conj' (x : Y) {J : Subgroup Y} (hJ : J ∈ Om R)
    (hJN : J ≤ Subgroup.normalizer (conjSub x K' : Set Y)) :
    J = conjSub x K' ∨ J = conjSub x (tightCore R) := by
  obtain ⟨y, hy, hy'⟩ := H.swap
  have hJN' : J ≤ Subgroup.normalizer (conjSub (x * y) (tightCore R) : Set Y) := by
    rwa [conjSub_mul, hy]
  rcases H.perp_conj (x * y) hJ hJN' with h | h
  · left
    rw [h, conjSub_mul, hy]
  · right
    rw [h, conjSub_mul, hy']

theorem mem_K1 : conjSub b (tightCore R) ∈ Om R := H.hypOmega.conjInvariant _ _ mem_K

theorem mem_K1' : conjSub b K' ∈ Om R := H.hypOmega.conjInvariant _ _ H.mem_K'

theorem iu1 : IsUniqueInvolution (conjSub b (tightCore R)) (b * t * b⁻¹) :=
  H.isUniqueInvolution_t.conj b

theorem iu1' : IsUniqueInvolution (conjSub b K') (b * t * b⁻¹) :=
  H.isUniqueInvolution_t'.conj b

theorem ne1 : conjSub b K' ≠ conjSub b (tightCore R) := fun h =>
  H.cfg.std.hne (conjSub_injective b h)

theorem K1_le_X : conjSub b (tightCore R) ≤ xA R A := (le_xA_iff H.mem_K1).mpr H.K_le

theorem K1'_le_X : conjSub b K' ≤ xA R A := (le_xA_iff H.mem_K1').mpr H.K'_le

theorem isPGroup_A : IsPGroup 2 A := by
  intro a
  refine ⟨1, Subtype.ext ?_⟩
  simp only [pow_one, Subgroup.coe_pow, pow_two, Subgroup.coe_one]
  exact H.e64.2.1 a a.2

theorem A_ne_bot : A ≠ ⊥ := by
  intro h
  have := H.e64.2.2
  rw [h, Subgroup.card_bot] at this
  norm_num at this

theorem card_lt : Nat.card (xA R A) < n := by
  have hC := H.cfg.std.perp.core
  haveI := hC.simple
  have hne := ne_top_of_le_normalizer hC.nonab H.A_ne_bot H.isPGroup_A (xA_le R A)
  rw [← hC.card]
  exact lt_of_le_of_ne (Subgroup.card_le_card_group _) fun heq =>
    hne ((Subgroup.card_eq_iff_eq_top _).mp heq)

theorem mem_restrict {J : Subgroup Y} (hJ : J ∈ Om R) (hJX : J ≤ xA R A) :
    J.subgroupOf (xA R A) ∈ restrictFamily (Om R) (xA R A) := ⟨J, hJ, hJX, rfl⟩

theorem hΩX : HypOmegaGen (restrictFamily (Om R) (xA R A)) :=
  hypOmegaGen_restrict H.hypOmega _

theorem h2X : ∀ L ∈ restrictFamily (Om R) (xA R A), IsPGroup 2 L := by
  rintro _ ⟨L, hL, -, rfl⟩
  exact (H.two L hL).comap_subtype

theorem conj_le_X {L : Subgroup Y} (hLX : L ≤ xA R A) {x : Y} (hx : x ∈ xA R A) :
    conjSub x L ≤ xA R A := by
  have := conjSub_mono (n := x) hLX
  rwa [conjSub_eq_self_of_mem hx] at this

theorem exists_conj_of_conj {L J : Subgroup Y} (hL : L ∈ Om R) (hJ : J ∈ Om R)
    (hLX : L ≤ xA R A) (hJX : J ≤ xA R A)
    (h : ∃ g : SecQuot (xA R A), conjSub g (secImage (xA R A) L) = secImage (xA R A) J) :
    ∃ x ∈ xA R A, conjSub x L = J := by
  obtain ⟨g, hg⟩ := h
  obtain ⟨x, rfl⟩ := QuotientGroup.mk'_surjective (classicalInvolutionOddCore ↥(xA R A)) g
  have hg' : secImage (xA R A) (conjSub (x : Y) L) = secImage (xA R A) J := by
    rw [SectionThmD.secImage_conjSub]
    exact hg
  have hxL : conjSub (x : Y) L ≤ xA R A := H.conj_le_X hLX x.2
  obtain ⟨m, hm, hmJ⟩ := OddQuot.exists_conj_of_map_eq H.hΩX H.h2X
    (CFSG.ComponentClassification.OddCore.odd_card _)
    (H.mem_restrict (H.hypOmega.conjInvariant _ _ hL) hxL) (H.mem_restrict hJ hJX) hg'
  rw [Generic.conjSub_subgroupOf] at hmJ
  have hmJX : conjSub (m : Y) J ≤ xA R A := H.conj_le_X hJX m.2
  have h1 := Subgroup.subgroupOf_inj.mp hmJ
  rw [inf_eq_left.mpr hmJX, inf_eq_left.mpr hxL] at h1
  refine ⟨(m : Y)⁻¹ * x, (xA R A).mul_mem ((xA R A).inv_mem m.2) x.2, ?_⟩
  rw [conjSub_mul, ← h1, conjSub_inv_conjSub]

theorem comm_of_not_conj (hT : Thm4RTwinBelow 3 n) {L J : Subgroup Y} (hL : L ∈ Om R)
    (hJ : J ∈ Om R) (hLX : L ≤ xA R A) (hJX : J ≤ xA R A)
    (hnc : ¬ ∃ g : SecQuot (xA R A), conjSub g (secImage (xA R A) L) = secImage (xA R A) J) :
    Commutes (secImage (xA R A) L) (secImage (xA R A) J) := by
  set X := xA R A with hX
  have hNodd := CFSG.ComponentClassification.OddCore.odd_card ↥X
  have hAX : ∀ L ∈ restrictFamily (Om R) X, AEmpty (restrictFamily (Om R) X) L := by
    rintro _ ⟨L, hL, hLX, rfl⟩
    exact aEmpty_restrictFamily H.hypOmega H.two subset_rfl hLX (H.aEmpty hL)
  have hΔ1 := OddQuot.hypOmegaGen_quotFamily H.hΩX H.h2X hNodd
  have hΔA := OddQuot.aEmpty_quotFamily H.hΩX H.h2X hNodd hAX
  have hmemΔ : ∀ {L : Subgroup Y}, L ∈ Om R → L ≤ X → secImage X L ∈
      quotFamily (restrictFamily (Om R) X) (classicalInvolutionOddCore ↥X) :=
    fun hL hLX => ⟨_, ⟨_, hL, hLX, rfl⟩, rfl⟩
  have hΔ2' : ∀ M ∈ quotFamily (restrictFamily (Om R) X) (classicalInvolutionOddCore ↥X),
      IsPGroup 2 M := by
    rintro _ ⟨_, ⟨L, hL, -, rfl⟩, rfl⟩
    exact (H.two L hL).comap_subtype.map _
  have hΔ2 : ∀ M ∈ quotFamily (restrictFamily (Om R) X) (classicalInvolutionOddCore ↥X),
      IsPGroup 2 (↥M ⧸ classicalInvolutionOddCore ↥M) := fun M hM =>
    (hΔ2' M hM).to_quotient (classicalInvolutionOddCore ↥M)
  have hΔq : ∀ M ∈ quotFamily (restrictFamily (Om R) X) (classicalInvolutionOddCore ↥X),
      ∀ P : Subgroup (SecQuot X), IsSylow2In P M →
        Nonempty (↥P ≃* QuaternionGroup (2 ^ (3 - 2))) := by
    rintro _ ⟨_, ⟨L, hL, hLX, rfl⟩, rfl⟩ P hP
    have hM2 : IsPGroup 2 (secImage X L) := SectionThmD.isPGroup_secImage (H.two L hL)
    have hPM : P = secImage X L := (hP.2.2 _ le_rfl hM2 hP.1).symm
    obtain ⟨e8⟩ := H.q8_of_mem hL
    exact ⟨(MulEquiv.subgroupCongr hPM).trans
      ((SectionThmD.secImageEquiv hLX (H.two L hL)).trans e8)⟩
  have hodd : classicalInvolutionOddCore (SecQuot X) = ⊥ :=
    CFSG.ComponentClassification.OddCore.quotient_corefree ↥X
  have hcard : Nat.card (SecQuot X) < n :=
    lt_of_le_of_lt (Nat.le_of_dvd Nat.card_pos (Subgroup.index_dvd_card _)) H.card_lt
  exact hT (SecQuot X) hcard _ hΔ1 hΔ2 hΔq hΔA hodd _ (hmemΔ hL hLX) _ (hmemΔ hJ hJX) hnc

theorem trans1 (hT : Thm4RTwinBelow 3 n) {J : Subgroup Y} (hJ : J ∈ Om R)
    (hJX : J ≤ xA R A) :
    (∃ x ∈ xA R A, conjSub x (conjSub b (tightCore R)) = J) ∨
      ∃ x ∈ xA R A, conjSub x (conjSub b K') = J := by
  by_cases hc : ∃ g : SecQuot (xA R A),
      conjSub g (secImage (xA R A) (conjSub b (tightCore R))) = secImage (xA R A) J
  · exact Or.inl (H.exists_conj_of_conj H.mem_K1 hJ H.K1_le_X hJX hc)
  · have hcomm := H.comm_of_not_conj hT H.mem_K1 hJ H.K1_le_X hJX hc
    set X := xA R A with hX
    have hJN : secImage X J ≤
        Subgroup.normalizer (secImage X (conjSub b (tightCore R)) : Set (SecQuot X)) :=
      TC.Thin.le_normalizer_of_comm fun y hy x hx => (hcomm x hx y hy).symm
    obtain ⟨m, hm, hmN⟩ := OddQuot.exists_conj_normalized
      (CFSG.ComponentClassification.OddCore.odd_card ↥X)
      (U := J.subgroupOf X) (K := (conjSub b (tightCore R)).subgroupOf X)
      (H.two J hJ).comap_subtype (H.two _ H.mem_K1).comap_subtype
      (fun u hu => hJN ⟨u, hu, rfl⟩)
    rw [Generic.conjSub_subgroupOf] at hmN
    have hmX : conjSub (m : Y) (conjSub b (tightCore R)) ≤ X := H.conj_le_X H.K1_le_X m.2
    have hJN' : J ≤ Subgroup.normalizer (conjSub ((m : Y) * b) (tightCore R) : Set Y) := by
      rw [conjSub_mul]
      exact le_normalizer_of_subgroupOf hJX hmX hmN
    rcases H.perp_conj ((m : Y) * b) hJ hJN' with h | h
    · exact Or.inl ⟨m, m.2, by rw [h, conjSub_mul]⟩
    · exact Or.inr ⟨m, m.2, by rw [h, conjSub_mul]⟩

theorem zA (hT : Thm4RTwinBelow 3 n) {J : Subgroup Y} (hJ : J ∈ Om R) (hJX : J ≤ xA R A)
    {z : Y} (hz : IsUniqueInvolution J z) : z ∈ A := by
  have hmem : ∀ x ∈ xA R A, x * (b * t * b⁻¹) * x⁻¹ ∈ A := fun x hx =>
    (Subgroup.mem_normalizer_iff.mp (xA_le R A hx) _).mp H.tA
  rcases H.trans1 hT hJ hJX with ⟨x, hx, rfl⟩ | ⟨x, hx, rfl⟩
  · rw [hz.eq (H.iu1.conj x)]
    exact hmem x hx
  · rw [hz.eq (H.iu1'.conj x)]
    exact hmem x hx

theorem oddCore_le_center (hT : Thm4RTwinBelow 3 n) :
    classicalInvolutionOddCore ↥(xA R A) ≤ Subgroup.center ↥(xA R A) := by
  have hc := AAE7.comm_of_mem_oddCoreOf H.hypOmega H.two (X := xA R A) (V := A)
    (fun x hx v hv => (Subgroup.mem_normalizer_iff.mp (xA_le R A hx) v).mp hv) H.isPGroup_A
    (P := famA R A) (fun L hL => hL.1) (fun L hL => TC.Thin.le_pSpan hL)
    (fun L hL x hx => conjSub_mem_famA (xA_le R A hx) hL)
    (fun L hL z hz => H.zA hT hL.1 (TC.Thin.le_pSpan hL) hz) le_rfl
  intro r hr
  rw [Subgroup.mem_center_iff]
  intro y
  exact Subtype.ext (hc r ⟨r, hr, rfl⟩ y y.2).symm

theorem eq_of_secImage_eq (hT : Thm4RTwinBelow 3 n) {J J' : Subgroup Y} (hJ : J ∈ Om R)
    (hJ' : J' ∈ Om R) (hJX : J ≤ xA R A) (hJ'X : J' ≤ xA R A)
    (h : secImage (xA R A) J = secImage (xA R A) J') : J = J' := by
  have h1 := AAE7.eq_of_map_eq_central (H.oddCore_le_center hT)
    (CFSG.ComponentClassification.OddCore.odd_card _) (H.two J hJ).comap_subtype
    (H.two J' hJ').comap_subtype h
  have h2 := Subgroup.subgroupOf_inj.mp h1
  rwa [inf_eq_left.mpr hJX, inf_eq_left.mpr hJ'X] at h2

theorem comm_of_secImage_comm (hT : Thm4RTwinBelow 3 n) {J J' : Subgroup Y} (hJ' : J' ∈ Om R)
    (hJX : J ≤ xA R A) (hJ'X : J' ≤ xA R A)
    (hc : ∀ x ∈ secImage (xA R A) J, ∀ y ∈ secImage (xA R A) J', x * y = y * x) :
    ∀ x ∈ J, ∀ y ∈ J', x * y = y * x := by
  intro x hx y hy
  have hmx : QuotientGroup.mk' (classicalInvolutionOddCore ↥(xA R A)) ⟨x, hJX hx⟩ ∈
      secImage (xA R A) J := ⟨⟨x, hJX hx⟩, Subgroup.mem_subgroupOf.mpr hx, rfl⟩
  have hmy : QuotientGroup.mk' (classicalInvolutionOddCore ↥(xA R A)) ⟨y, hJ'X hy⟩ ∈
      secImage (xA R A) J' := ⟨⟨y, hJ'X hy⟩, Subgroup.mem_subgroupOf.mpr hy, rfl⟩
  obtain ⟨a, ha⟩ := OddQuot.two_elt (H.two J' hJ') hy
  have hya : (⟨y, hJ'X hy⟩ : ↥(xA R A)) ^ 2 ^ a = 1 := Subtype.ext (by simpa using ha)
  exact congrArg Subtype.val (AAE7.comm_of_mk_comm (H.oddCore_le_center hT)
    (CFSG.ComponentClassification.OddCore.odd_card _) hya (hc _ hmx _ hmy))

theorem K1'_conj (hT : Thm4RTwinBelow 3 n) :
    ∃ x ∈ xA R A, conjSub x (conjSub b (tightCore R)) = conjSub b K' := by
  by_contra hcon
  set X := xA R A with hX
  have hall : ∀ J ∈ Om R, J ≤ X → J = conjSub b (tightCore R) ∨ J = conjSub b K' := by
    intro J hJ hJX
    rcases H.trans1 hT hJ hJX with ⟨x, hx, hxJ⟩ | ⟨x, hx, hxJ⟩
    · have hnc : ¬ ∃ g : SecQuot X,
          conjSub g (secImage X (conjSub b K')) = secImage X J := by
        intro hg
        obtain ⟨y, hy, hyJ⟩ := H.exists_conj_of_conj H.mem_K1' hJ H.K1'_le_X hJX hg
        exact hcon ⟨y⁻¹ * x, X.mul_mem (X.inv_mem hy) hx, by
          rw [conjSub_mul, hxJ, ← hyJ, conjSub_inv_conjSub]⟩
      have hcY := H.comm_of_secImage_comm hT hJ H.K1'_le_X hJX
        (H.comm_of_not_conj hT H.mem_K1' hJ H.K1'_le_X hJX hnc)
      have hJN : J ≤ Subgroup.normalizer (conjSub b K' : Set Y) :=
        TC.Thin.le_normalizer_of_comm fun y hy x hx => (hcY x hx y hy).symm
      rcases H.perp_conj' b hJ hJN with h | h
      · exact absurd ⟨x, hx, hxJ.trans h⟩ hcon
      · exact Or.inl h
    · have hnc : ¬ ∃ g : SecQuot X,
          conjSub g (secImage X (conjSub b (tightCore R))) = secImage X J := by
        intro hg
        obtain ⟨y, hy, hyJ⟩ := H.exists_conj_of_conj H.mem_K1 hJ H.K1_le_X hJX hg
        exact hcon ⟨x⁻¹ * y, X.mul_mem (X.inv_mem hx) hy, by
          rw [conjSub_mul, hyJ, ← hxJ, conjSub_inv_conjSub]⟩
      have hcY := H.comm_of_secImage_comm hT hJ H.K1_le_X hJX
        (H.comm_of_not_conj hT H.mem_K1 hJ H.K1_le_X hJX hnc)
      have hJN : J ≤ Subgroup.normalizer (conjSub b (tightCore R) : Set Y) :=
        TC.Thin.le_normalizer_of_comm fun y hy x hx => (hcY x hx y hy).symm
      rcases H.perp_conj b hJ hJN with h | h
      · exact absurd ⟨x⁻¹, X.inv_mem hx, by rw [← h, ← hxJ, conjSub_inv_conjSub]⟩ hcon
      · exact Or.inr h
  have hsub : {J | J ∈ Om R ∧ J ≤ Subgroup.normalizer (A : Set Y) ∧
      J ≤ Subgroup.centralizer ({e} : Set Y)} ⊆ {conjSub b (tightCore R), conjSub b K'} := by
    rintro J ⟨hJ, hJA, -⟩
    rcases hall J hJ ((le_xA_iff hJ).mpr hJA) with h | h
    · exact Or.inl h
    · exact Or.inr h
  have h1 := Set.ncard_le_ncard hsub (Set.toFinite _)
  have h2 : ({conjSub b (tightCore R), conjSub b K'} : Set (Subgroup Y)).ncard ≤ 2 :=
    (Set.ncard_insert_le _ _).trans (by rw [Set.ncard_singleton])
  have h3 := H.cnt.1
  omega

theorem trans (hT : Thm4RTwinBelow 3 n) {J : Subgroup Y} (hJ : J ∈ Om R) (hJX : J ≤ xA R A) :
    ∃ x : xA R A, conjSub (x : Y) (conjSub b (tightCore R)) = J := by
  rcases H.trans1 hT hJ hJX with ⟨x, hx, hxJ⟩ | ⟨x, hx, hxJ⟩
  · exact ⟨⟨x, hx⟩, hxJ⟩
  · obtain ⟨y, hy, hyK⟩ := H.K1'_conj hT
    exact ⟨⟨x * y, (xA R A).mul_mem hx hy⟩, by rw [conjSub_mul, hyK, hxJ]⟩

theorem gen (hT : Thm4RTwinBelow 3 n) :
    (⨆ x : xA R A, conjSub (x : Y) (conjSub b (tightCore R))) = xA R A := by
  refine le_antisymm (iSup_le fun x => H.conj_le_X H.K1_le_X x.2)
    (TC.Thin.pSpan_le fun J hJ => ?_)
  obtain ⟨x, hx⟩ := H.trans hT hJ.1 (TC.Thin.le_pSpan hJ)
  rw [← hx]
  exact le_iSup (fun x : xA R A => conjSub (x : Y) (conjSub b (tightCore R))) x

theorem normA : ∀ x ∈ xA R A, ∀ v ∈ A, x * v * x⁻¹ ∈ A := fun x hx v hv =>
  (Subgroup.mem_normalizer_iff.mp (xA_le R A hx) v).mp hv

theorem thmDHyp (hT : Thm4RTwinBelow 3 n) :
    ThmDHyp 3 (SectionThmD.secClass (xA R A) (conjSub b (tightCore R))) :=
  SectionThmD.thmDHyp_secClass H.hypOmega H.two H.mem_K1 (H.card_of_mem H.mem_K1)
    (H.aEmpty H.mem_K1) H.K1_le_X (H.gen hT) H.iu1 H.normA H.isPGroup_A H.tA

theorem thmDConcl (hP : TL4.TightBelowRPlus 3 n) (hT : Thm4RTwinBelow 3 n) :
    ThmDConcl (SectionThmD.secClass (xA R A) (conjSub b (tightCore R))) :=
  SectionThmD.thmDConcl_at_section H.hypOmega H.two H.mem_K1 (H.card_of_mem H.mem_K1)
    (H.aEmpty H.mem_K1) H.K1_le_X (H.gen hT) H.iu1 H.normA H.isPGroup_A H.tA hP.thmD.d2
    H.card_lt

theorem oddCore_span_eq_bot (hT : Thm4RTwinBelow 3 n) :
    classicalInvolutionOddCore
      ↥(pSpan (SectionThmD.secClass (xA R A) (conjSub b (tightCore R)))) = ⊥ :=
  classicalInvolutionOddCore_eq_bot_of_mulEquiv
    ((MulEquiv.subgroupCongr (H.thmDHyp hT).gen).trans Subgroup.topEquiv).symm
    (CFSG.ComponentClassification.OddCore.quotient_corefree ↥(xA R A))

theorem secImage_mem_secClass (x : xA R A) :
    secImage (xA R A) (conjSub (x : Y) (conjSub b (tightCore R))) ∈
      SectionThmD.secClass (xA R A) (conjSub b (tightCore R)) :=
  SectionThmD.mem_secClass_iff.mpr ⟨x, rfl⟩

theorem K1'_mem_secClass (hT : Thm4RTwinBelow 3 n) :
    secImage (xA R A) (conjSub b K') ∈ SectionThmD.secClass (xA R A) (conjSub b (tightCore R)) := by
  obtain ⟨x, hx, hxK⟩ := H.K1'_conj hT
  have := H.secImage_mem_secClass ⟨x, hx⟩
  rwa [show conjSub x (conjSub b (tightCore R)) = conjSub b K' from hxK] at this

theorem secImage_ne (hT : Thm4RTwinBelow 3 n) :
    secImage (xA R A) (conjSub b (tightCore R)) ≠ secImage (xA R A) (conjSub b K') := fun h =>
  H.ne1 (H.eq_of_secImage_eq hT H.mem_K1 H.mem_K1' H.K1_le_X H.K1'_le_X h).symm

theorem false_of_single (hT : Thm4RTwinBelow 3 n)
    (hsing : ∀ L ∈ SectionThmD.secClass (xA R A) (conjSub b (tightCore R)),
      ∀ L' ∈ SectionThmD.secClass (xA R A) (conjSub b (tightCore R)), L = L') : False :=
  H.secImage_ne hT (hsing _ (CoreAssembly.mem_conjClass_self _) _ (H.K1'_mem_secClass hT))

theorem false_of_e8 (hT : Thm4RTwinBelow 3 n) {E' : Subgroup (SecQuot (xA R A))}
    (hE : E8Struct ⊤ E') : False := by
  have h1 := SectionThmD.isUniqueInvolution_secImage H.K1_le_X (H.two _ H.mem_K1) H.iu1
  have h2 := SectionThmD.isUniqueInvolution_secImage H.K1'_le_X (H.two _ H.mem_K1') H.iu1'
  exact H.secImage_ne hT (eq_of_inv_e8 (H.thmDHyp hT) hE (CoreAssembly.mem_conjClass_self _)
    (H.K1'_mem_secClass hT) h1 h2)

theorem eq_K1'_of_comm {J : Subgroup Y} (hJ : J ∈ Om R) (hne : J ≠ conjSub b (tightCore R))
    (hc : ∀ x ∈ conjSub b (tightCore R), ∀ y ∈ J, x * y = y * x) : J = conjSub b K' := by
  have hJN : J ≤ Subgroup.normalizer (conjSub b (tightCore R) : Set Y) :=
    le_normalizer_of_comm fun x hx y hy => (hc y hy x hx).symm
  rcases H.perp_conj b hJ hJN with h | h
  · exact absurd h hne
  · exact h

theorem eq_K1'_of_phi_comm (hT : Thm4RTwinBelow 3 n) {M : Type} [Group M]
    (φ : ↥(pSpan (SectionThmD.secClass (xA R A) (conjSub b (tightCore R)))) →* M)
    (hk : IsPGroup 2 φ.ker) {L : Subgroup (SecQuot (xA R A))}
    (hL : L ∈ SectionThmD.secClass (xA R A) (conjSub b (tightCore R)))
    (hne : L ≠ secImage (xA R A) (conjSub b (tightCore R)))
    (hc : ∀ x ∈ ((secImage (xA R A) (conjSub b (tightCore R))).subgroupOf
        (pSpan (SectionThmD.secClass (xA R A) (conjSub b (tightCore R))))).map φ,
      ∀ y ∈ (L.subgroupOf (pSpan (SectionThmD.secClass (xA R A) (conjSub b (tightCore R))))).map φ,
        x * y = y * x) :
    L = secImage (xA R A) (conjSub b K') := by
  have hD := H.thmDHyp hT
  have hK : secImage (xA R A) (conjSub b (tightCore R)) ∈
      SectionThmD.secClass (xA R A) (conjSub b (tightCore R)) := CoreAssembly.mem_conjClass_self _
  have hcb := comm_of_phi_comm hD.hyp hD.two subset_rfl φ hk hK hL hne.symm hc
  obtain ⟨x, hx⟩ := SectionThmD.mem_secClass_iff.mp hL
  have hJ : conjSub (x : Y) (conjSub b (tightCore R)) ∈ Om R :=
    H.hypOmega.conjInvariant _ _ H.mem_K1
  have hcY := H.comm_of_secImage_comm hT hJ H.K1_le_X (H.conj_le_X H.K1_le_X x.2)
    (by rw [hx]; exact hcb)
  have hJne : conjSub (x : Y) (conjSub b (tightCore R)) ≠ conjSub b (tightCore R) := fun h =>
    hne (by rw [← hx, h])
  rw [← hx, H.eq_K1'_of_comm hJ hJne hcY]

theorem false_of_ae_ge8 (hT : Thm4RTwinBelow 3 n) {m : ℕ} (hm : 8 ≤ m)
    (I : AEIdent (SectionThmD.secClass (xA R A) (conjSub b (tightCore R))) m) : False := by
  have hk : IsPGroup 2 I.φ.ker := I.isPGroup_ker (H.oddCore_span_eq_bot hT)
  have hn5 : 5 ≤ m := by omega
  have hK : secImage (xA R A) (conjSub b (tightCore R)) ∈
      SectionThmD.secClass (xA R A) (conjSub b (tightCore R)) := CoreAssembly.mem_conjClass_self _
  obtain ⟨α, hα, b₀, hlab₀⟩ := I.label _ hK
  obtain ⟨β, hβsub, hβ⟩ : ∃ β ⊆ Finset.univ \ α, β.card = 4 := Finset.exists_subset_card_eq (by
    rw [Finset.card_sdiff_of_subset (Finset.subset_univ _), Finset.card_univ, Fintype.card_fin, hα]
    omega)
  have hd : Disjoint α β := Finset.disjoint_of_subset_right hβsub Finset.disjoint_sdiff
  have hcomm : ∀ {L : Subgroup (SecQuot (xA R A))} {c : Bool},
      L ∈ SectionThmD.secClass (xA R A) (conjSub b (tightCore R)) →
      (L.subgroupOf (pSpan (SectionThmD.secClass (xA R A) (conjSub b (tightCore R))))).map I.φ =
        AE.memBar β hβ c → L = secImage (xA R A) (conjSub b K') := by
    intro L c hL hlab
    have hne : L ≠ secImage (xA R A) (conjSub b (tightCore R)) := by
      intro h
      rw [h, hlab₀] at hlab
      have hαβ : α = β := AE.eq_of_memBar_eq' hn5 hlab
      subst hαβ
      have h0 : α = ∅ := disjoint_self.mp hd
      rw [h0, Finset.card_empty] at hα
      omega
    exact H.eq_K1'_of_phi_comm hT I.φ hk hL hne
      (by rw [hlab₀, hlab]; exact AE.comm_memBar_of_disjoint hd b₀ c)
  obtain ⟨L₁, hL₁, hlab₁⟩ := I.label_surj β hβ true
  obtain ⟨L₂, hL₂, hlab₂⟩ := I.label_surj β hβ false
  have h12 : L₁ = L₂ := (hcomm hL₁ hlab₁).trans (hcomm hL₂ hlab₂).symm
  rw [h12] at hlab₁
  exact AE.memBar_true_ne_false hn5 β hβ (hlab₁.symm.trans hlab₂)

theorem false_of_e29 (hT : Thm4RTwinBelow 3 n)
    (I : AEIdentOn (SectionThmD.secClass (xA R A) (conjSub b (tightCore R))) 8 AE.e29Sets
      AE.e29Sub) : False := by
  have hk : IsPGroup 2 I.φ.ker := I.toLabel.isPGroup_ker (H.oddCore_span_eq_bot hT)
  have hK : secImage (xA R A) (conjSub b (tightCore R)) ∈
      SectionThmD.secClass (xA R A) (conjSub b (tightCore R)) := CoreAssembly.mem_conjClass_self _
  obtain ⟨α, hαS, hα, b₀, hlab₀⟩ := I.label _ hK
  have hβS : αᶜ ∈ AE.e29Sets := AE.e29Sets_compl hαS
  have hβ : αᶜ.card = 4 := by
    rw [Finset.card_compl, Fintype.card_fin, hα]
  have hd : Disjoint α αᶜ := disjoint_compl_right
  have hcomm : ∀ {L : Subgroup (SecQuot (xA R A))} {c : Bool},
      L ∈ SectionThmD.secClass (xA R A) (conjSub b (tightCore R)) →
      (L.subgroupOf (pSpan (SectionThmD.secClass (xA R A) (conjSub b (tightCore R))))).map I.φ =
        AE.memBar αᶜ hβ c → L = secImage (xA R A) (conjSub b K') := by
    intro L c hL hlab
    have hne : L ≠ secImage (xA R A) (conjSub b (tightCore R)) := by
      intro h
      rw [h, hlab₀] at hlab
      have hαβ : α = αᶜ := AE.eq_of_memBar_eq' (by norm_num) hlab
      have h0 : α = ∅ := by
        have := hd
        rw [← hαβ] at this
        exact disjoint_self.mp this
      rw [h0, Finset.card_empty] at hα
      omega
    exact H.eq_K1'_of_phi_comm hT I.φ hk hL hne
      (by rw [hlab₀, hlab]; exact AE.comm_memBar_of_disjoint hd b₀ c)
  obtain ⟨L₁, hL₁, hlab₁⟩ := I.label_surj αᶜ hβS hβ true
  obtain ⟨L₂, hL₂, hlab₂⟩ := I.label_surj αᶜ hβS hβ false
  have h12 : L₁ = L₂ := (hcomm hL₁ hlab₁).trans (hcomm hL₂ hlab₂).symm
  rw [h12] at hlab₁
  exact AE.memBar_true_ne_false (by norm_num) αᶜ hβ (hlab₁.symm.trans hlab₂)

theorem mem_secClass_of (hT : Thm4RTwinBelow 3 n) {J : Subgroup Y} (hJ : J ∈ Om R)
    (hJX : J ≤ xA R A) :
    secImage (xA R A) J ∈ SectionThmD.secClass (xA R A) (conjSub b (tightCore R)) := by
  obtain ⟨x, hx⟩ := H.trans hT hJ hJX
  rw [← hx]
  exact H.secImage_mem_secClass x

theorem secAutX_mem_secClass (hT : Thm4RTwinBelow 3 n) {x : Y}
    (hx : x ∈ Subgroup.normalizer (A : Set Y)) {L : Subgroup (SecQuot (xA R A))}
    (hL : L ∈ SectionThmD.secClass (xA R A) (conjSub b (tightCore R))) :
    L.map (secAutX (xA R A) (mem_normalizer_xA (R := R) hx)).toMonoidHom ∈
      SectionThmD.secClass (xA R A) (conjSub b (tightCore R)) := by
  obtain ⟨y, rfl⟩ := SectionThmD.mem_secClass_iff.mp hL
  rw [map_secAutX_secImage]
  have hmem : conjSub (y : Y) (conjSub b (tightCore R)) ∈ famA R A :=
    ⟨H.hypOmega.conjInvariant _ _ H.mem_K1, (H.conj_le_X H.K1_le_X y.2).trans (xA_le R A)⟩
  have h2 := conjSub_mem_famA hx hmem
  exact H.mem_secClass_of hT h2.1 ((le_xA_iff h2.1).mpr h2.2)

theorem secAutX_symm_mem_secClass (hT : Thm4RTwinBelow 3 n) {x : Y}
    (hx : x ∈ Subgroup.normalizer (A : Set Y)) {L : Subgroup (SecQuot (xA R A))}
    (hL : L ∈ SectionThmD.secClass (xA R A) (conjSub b (tightCore R))) :
    L.map (secAutX (xA R A) (mem_normalizer_xA (R := R) hx)).symm.toMonoidHom ∈
      SectionThmD.secClass (xA R A) (conjSub b (tightCore R)) := by
  obtain ⟨y, rfl⟩ := SectionThmD.mem_secClass_iff.mp hL
  rw [map_secAutX_symm_secImage]
  have hmem : conjSub (y : Y) (conjSub b (tightCore R)) ∈ famA R A :=
    ⟨H.hypOmega.conjInvariant _ _ H.mem_K1, (H.conj_le_X H.K1_le_X y.2).trans (xA_le R A)⟩
  have h2 := conjSub_mem_famA (inv_mem hx) hmem
  exact H.mem_secClass_of hT h2.1 ((le_xA_iff h2.1).mpr h2.2)

theorem false_of_wSet (hT : Thm4RTwinBelow 3 n) {V : Subgroup (SecQuot (xA R A))}
    (hW : WSet (SectionThmD.secClass (xA R A) (conjSub b (tightCore R))) = {V}) : False := by
  obtain ⟨x, hx, K, hK, hKA, hxK, hU⟩ := H.w
  have hxX : x ∈ Subgroup.normalizer (xA R A : Set Y) := mem_normalizer_xA hx
  set σ := secAutX (xA R A) hxX with hσ
  have hD := H.thmDHyp hT
  have hVmem : V ∈ WSet (SectionThmD.secClass (xA R A) (conjSub b (tightCore R))) := by
    rw [hW]
    rfl
  have hσV : V.map σ.toMonoidHom = V := by
    have := TwinPerpV3.Pf93.map_mem_WSet_equiv σ (fun L hL => H.secAutX_mem_secClass hT hx hL)
      (fun L hL => H.secAutX_symm_mem_secClass hT hx hL) hVmem
    rw [hW] at this
    exact this
  have hKX : K ≤ xA R A := (le_xA_iff hK).mpr hKA
  have hKc : secImage (xA R A) K ∈ SectionThmD.secClass (xA R A) (conjSub b (tightCore R)) :=
    H.mem_secClass_of hT hK hKX
  have h4 := TL4.card_inf_of_wSet_eq hD hW _ hKc
  set U' : Subgroup (xA R A) :=
    V.comap (QuotientGroup.mk' (classicalInvolutionOddCore ↥(xA R A))) ⊓
      K.subgroupOf (xA R A) with hU'
  have hU'map : U'.map (QuotientGroup.mk' (classicalInvolutionOddCore ↥(xA R A))) =
      secImage (xA R A) K ⊓ V := by
    apply le_antisymm
    · rintro _ ⟨y, hy, rfl⟩
      exact ⟨⟨y, hy.2, rfl⟩, hy.1⟩
    · rintro _ ⟨⟨y, hy, rfl⟩, hyV⟩
      exact ⟨y, ⟨hyV, hy⟩, rfl⟩
  have hU'N : U' ⊓ classicalInvolutionOddCore ↥(xA R A) = ⊥ :=
    eq_bot_iff.mpr ((inf_le_inf_right _ inf_le_right).trans
      (SectionThmD.subgroupOf_inf_oddCore_eq_bot (H.two K hK)).le)
  have hU'card : Nat.card U' = 4 := by
    rw [← h4, ← hU'map]
    exact Nat.card_congr (AscQuot.quotRestrictEquiv hU'N).toEquiv
  set U : Subgroup Y := U'.map (xA R A).subtype with hUdef
  have hUK : U ≤ K := by
    rintro _ ⟨y, hy, rfl⟩
    exact Subgroup.mem_subgroupOf.mp hy.2
  have hUcard : Nat.card U = 4 := by
    rw [hUdef, Subgroup.card_map_of_injective (xA R A).subtype_injective, hU'card]
  obtain ⟨z, hz⟩ := Sec6Gen.exists_uniqueInvolution H.hypOmega hK
  have hUcyc : IsCyclic U := isCyclic_of_card_four hz hUK hUcard
  have hle : conjSub x U ≤ U := by
    rintro _ ⟨_, ⟨u', hu', rfl⟩, rfl⟩
    refine ⟨conjX (xA R A) hxX u', Subgroup.mem_inf.mpr ⟨?_, Subgroup.mem_subgroupOf.mpr ?_⟩,
      rfl⟩
    · show QuotientGroup.mk' (classicalInvolutionOddCore ↥(xA R A)) (conjX (xA R A) hxX u') ∈ V
      rw [← secAutX_mk, ← hσV]
      exact ⟨_, (Subgroup.mem_inf.mp hu').1, rfl⟩
    · rw [conjX_apply]
      have := conj_mem_conjSub (n := x)
        (Subgroup.mem_subgroupOf.mp (Subgroup.mem_inf.mp hu').2)
      rwa [hxK] at this
  have hxU : conjSub x U = U := Subgroup.eq_of_le_of_card_ge hle
    (le_of_eq (Subgroup.card_map_of_injective (MulAut.conj x).injective).symm)
  exact hU U hUK hUcyc hUcard hxU

theorem e_mem_normalizer : e ∈ Subgroup.normalizer (A : Set Y) := Subgroup.le_normalizer H.eA

theorem e_comm {z : Y} (hz : z ∈ A) : e * z = z * e := H.e64.1 e H.eA z hz

theorem fix_inv {L : Subgroup (SecQuot (xA R A))}
    (hL : L ∈ SectionThmD.secClass (xA R A) (conjSub b (tightCore R))) {q : SecQuot (xA R A)}
    (hq : IsUniqueInvolution L q) :
    secAutX (xA R A) (mem_normalizer_xA (R := R) H.e_mem_normalizer) q = q := by
  obtain ⟨y, rfl⟩ := SectionThmD.mem_secClass_iff.mp hL
  have hu := SectionThmD.isUniqueInvolution_secImage_conjSub H.K1_le_X (H.two _ H.mem_K1) H.iu1 y
  rw [hq.eq hu]
  unfold secInv
  rw [secAutX_mk]
  congr 1
  apply Subtype.ext
  rw [conjX_apply]
  have hwA : ((y * ⟨b * t * b⁻¹, H.K1_le_X H.iu1.mem⟩ * y⁻¹ : ↥(xA R A)) : Y) ∈ A :=
    H.normA y y.2 _ H.tA
  rw [H.e_comm hwA, mul_inv_cancel_right]

theorem fix_iff_cent (hT : Thm4RTwinBelow 3 n) {J : Subgroup Y} (hJ : J ∈ Om R)
    (hJX : J ≤ xA R A) :
    (∀ q ∈ secImage (xA R A) J,
      secAutX (xA R A) (mem_normalizer_xA (R := R) H.e_mem_normalizer) q = q) ↔
        J ≤ Subgroup.centralizer ({e} : Set Y) := by
  have heX := mem_normalizer_xA (R := R) H.e_mem_normalizer
  constructor
  · intro hq j hj
    rw [Subgroup.mem_centralizer_singleton_iff]
    have h1 := hq _ ⟨⟨j, hJX hj⟩, Subgroup.mem_subgroupOf.mpr hj, rfl⟩
    rw [secAutX_mk] at h1
    have hmem := OddQuot.inv_mul_mem_of_mk_eq h1
    have hcen := H.oddCore_le_center hT hmem
    obtain ⟨k, hk⟩ := OddQuot.two_elt (H.two J hJ) hj
    have hc2 : (⟨j, hJX hj⟩ : ↥(xA R A)) ^ 2 ^ k = 1 := Subtype.ext (by simpa using hk)
    have ha2 : (conjX (xA R A) heX ⟨j, hJX hj⟩) ^ 2 ^ k = 1 := by
      rw [← map_pow, hc2, map_one]
    have hac : conjX (xA R A) heX ⟨j, hJX hj⟩ * ⟨j, hJX hj⟩ =
        ⟨j, hJX hj⟩ * conjX (xA R A) heX ⟨j, hJX hj⟩ := by
      generalize conjX (xA R A) heX ⟨j, hJX hj⟩ = a at hcen ⊢
      generalize (⟨j, hJX hj⟩ : ↥(xA R A)) = c at hcen ⊢
      have h2 := Subgroup.mem_center_iff.mp hcen a
      calc a * c = a * (a * (a⁻¹ * c)) := by group
        _ = a * ((a⁻¹ * c) * a) := by rw [h2]
        _ = c * a := by group
    have hae := OddQuot.eq_of_commute_of_mem (CFSG.ComponentClassification.OddCore.odd_card _)
      ⟨k, ha2⟩ ⟨k, hc2⟩ hac hmem
    have h3 : e * j * e⁻¹ = j := congrArg Subtype.val hae
    calc j * e = e * j * e⁻¹ * e := by rw [h3]
      _ = e * j := by group
  · intro hJe q hq
    obtain ⟨y, hy, rfl⟩ := hq
    rw [secAutX_mk]
    congr 1
    apply Subtype.ext
    rw [conjX_apply]
    have := Subgroup.mem_centralizer_singleton_iff.mp (hJe (Subgroup.mem_subgroupOf.mp hy))
    rw [← this, mul_inv_cancel_right]

theorem false_of_ae_le7 (hT : Thm4RTwinBelow 3 n) {m : ℕ}
    (hm5 : 5 ≤ m) (hm7 : m ≤ 7)
    (I : AEIdent (SectionThmD.secClass (xA R A) (conjSub b (tightCore R))) m) : False := by
  classical
  have hD := H.thmDHyp hT
  have hk : IsPGroup 2 I.φ.ker := I.isPGroup_ker (H.oddCore_span_eq_bot hT)
  have heX := mem_normalizer_xA (R := R) H.e_mem_normalizer
  obtain ⟨w, hw⟩ := exists_wr_of_aut hm5 hD.gen I (secAutX (xA R A) heX)
    (fun L hL => H.secAutX_mem_secClass hT H.e_mem_normalizer hL)
  have h8 : ∀ L ∈ SectionThmD.secClass (xA R A) (conjSub b (tightCore R)), Nat.card L = 8 :=
    fun L hL => (hD.card L hL).trans (by norm_num)
  have hperm : w.perm = 1 := by
    refine TwinThinPf18.perm_eq_one_of_cent_zBar hm5 w fun β hβ => ?_
    obtain ⟨L, hL, hlab⟩ := I.label_surj β hβ true
    obtain ⟨u, hu, hφu⟩ := TL4.AECov.exists_isUniqueInvolution I hm5 hL (h8 L hL) hlab
    have h1 := hw ⟨u, le_pSpan hL hu.mem⟩ ⟨u, le_pSpan hL hu.mem⟩ (H.fix_inv hL hu).symm
    rw [hφu] at h1
    exact h1.symm
  set v := w.vec with hv
  have hwv : w = AE.Wr.ofVec v := AE.Wr.ext rfl hperm
  have hfixIff : ∀ L ∈ SectionThmD.secClass (xA R A) (conjSub b (tightCore R)),
      ∀ (α : Finset (Fin m)) (h : α.card = 4) (c : Bool),
      (L.subgroupOf (pSpan (SectionThmD.secClass (xA R A) (conjSub b (tightCore R))))).map I.φ =
        AE.memBar α h c →
      ((∀ q ∈ L, secAutX (xA R A) heX q = q) ↔ ∀ i ∈ α, ∀ j ∈ α, v i = v j) := by
    intro L hL α h c hlab
    rw [← AE.vec_centralizes_memBar_iff hm5 α h c v, ← hlab, ← hwv]
    constructor
    · intro hq x hx
      obtain ⟨l, hl, rfl⟩ := I.exists_of_mem_map hL hx
      have h1 := hw ⟨l, le_pSpan hL hl⟩ ⟨l, le_pSpan hL hl⟩ (hq l hl).symm
      calc AE.mkQ m w * I.φ ⟨l, le_pSpan hL hl⟩
          = AE.mkQ m w * I.φ ⟨l, le_pSpan hL hl⟩ * (AE.mkQ m w)⁻¹ * AE.mkQ m w := by group
        _ = I.φ ⟨l, le_pSpan hL hl⟩ * AE.mkQ m w := by rw [← h1]
    · intro hc q hq
      have hcc : ∀ l (hl : l ∈ L), AE.mkQ m w * I.φ ⟨l, le_pSpan hL hl⟩ * (AE.mkQ m w)⁻¹ =
          I.φ ⟨l, le_pSpan hL hl⟩ := fun l hl => by
        rw [hc _ (I.mem_map hL hl), mul_inv_cancel_right]
      have hL' := H.secAutX_mem_secClass hT H.e_mem_normalizer hL
      obtain ⟨α', h', c', hlab'⟩ := I.label _ hL'
      have hle : ((L.map (secAutX (xA R A) heX).toMonoidHom).subgroupOf
          (pSpan (SectionThmD.secClass (xA R A) (conjSub b (tightCore R))))).map I.φ ≤
          (L.subgroupOf (pSpan (SectionThmD.secClass (xA R A) (conjSub b (tightCore R))))).map
            I.φ := by
        rintro _ ⟨y, hy, rfl⟩
        obtain ⟨l, hl, hly⟩ := Subgroup.mem_subgroupOf.mp hy
        have h1 := hw ⟨l, le_pSpan hL hl⟩ y hly.symm
        rw [h1, hcc l hl]
        exact I.mem_map hL hl
      have hσL : L.map (secAutX (xA R A) heX).toMonoidHom = L :=
        TL4.eq_of_map_le_memBar hD.hyp hD.two hm5 I.φ hk hL' hL (le_pSpan hL') (le_pSpan hL)
          hlab' hle
      have hσq : secAutX (xA R A) heX q ∈ L := by
        rw [← hσL]
        exact ⟨q, hq, rfl⟩
      have h1 := hw ⟨q, le_pSpan hL hq⟩ ⟨_, le_pSpan hL hσq⟩ rfl
      rw [hcc q hq] at h1
      exact TC.Thin.phi_injOn I.φ hm5 hL (h8 L hL) hlab hσq hq h1
  set M : Set (Subgroup Y) := {J | J ∈ Om R ∧ J ≤ Subgroup.normalizer (A : Set Y) ∧
    J ≤ Subgroup.centralizer ({e} : Set Y)} with hM
  set F : Subgroup Y → Finset (Fin m) × Bool := fun J => AAE7.labelOf I (secImage (xA R A) J)
    with hF
  have hXM : ∀ J ∈ M, J ≤ xA R A := fun J hJ => (le_xA_iff hJ.1).mpr hJ.2.1
  have hΦM : ∀ J ∈ M, secImage (xA R A) J ∈
      SectionThmD.secClass (xA R A) (conjSub b (tightCore R)) := fun J hJ =>
    H.mem_secClass_of hT hJ.1 (hXM J hJ)
  have hinj : Set.InjOn F M := by
    intro J hJ J' hJ' h
    have h1 := AAE7.map_eq_of_labelOf_eq I (hΦM J hJ) (hΦM J' hJ') h
    have h2 := aeIdent_eq_of_map_eq hD.hyp hD.two subset_rfl hm5 I hk (hΦM J hJ) (hΦM J' hJ') h1
    exact H.eq_of_secImage_eq hT hJ.1 hJ'.1 (hXM J hJ) (hXM J' hJ') h2
  have himg : F '' M =
      {p : Finset (Fin m) × Bool | p.1.card = 4 ∧ ∀ i ∈ p.1, ∀ j ∈ p.1, v i = v j} := by
    ext ⟨α, c⟩
    constructor
    · rintro ⟨J, hJ, hJF⟩
      obtain ⟨hp, hspec⟩ := AAE7.labelOf_spec I (hΦM J hJ)
      have hp' : α.card = 4 := by
        have := hp
        rw [show AAE7.labelOf I (secImage (xA R A) J) = (α, c) from hJF] at this
        exact this
      have hspec' := hspec.trans (AAE7.memBar_congr hJF hp hp')
      exact ⟨hp', (hfixIff _ (hΦM J hJ) α hp' c hspec').mp
        ((H.fix_iff_cent hT hJ.1 (hXM J hJ)).mpr hJ.2.2)⟩
    · rintro ⟨hα, hc⟩
      obtain ⟨L, hL, hlab⟩ := I.label_surj α hα c
      obtain ⟨y, rfl⟩ := SectionThmD.mem_secClass_iff.mp hL
      have hJ : conjSub (y : Y) (conjSub b (tightCore R)) ∈ Om R :=
        H.hypOmega.conjInvariant _ _ H.mem_K1
      have hJX := H.conj_le_X H.K1_le_X y.2
      have hJe := (H.fix_iff_cent hT hJ hJX).mp ((hfixIff _ hL α hα c hlab).mpr hc)
      exact ⟨_, ⟨hJ, hJX.trans (xA_le R A), hJe⟩, AAE7.labelOf_eq I hm5 hL hlab⟩
  have hset : {p : Finset (Fin m) × Bool | p.1.card = 4 ∧ ∀ i ∈ p.1, ∀ j ∈ p.1, v i = v j} =
      ↑(((Finset.univ.powersetCard 4 : Finset (Finset (Fin m))).filter
        (fun α => ∀ i ∈ α, ∀ j ∈ α, v i = v j)) ×ˢ (Finset.univ : Finset Bool)) := by
    ext p
    simp [Finset.mem_powersetCard]
  have hcard : M.ncard = ((Finset.univ.filter (fun i => v i = 1)).card.choose 4 +
      (Finset.univ.filter (fun i => v i = 1))ᶜ.card.choose 4) * 2 := by
    rw [← hinj.ncard_image, himg, hset, Set.ncard_coe_finset, Finset.card_product,
      card_const_sets, Finset.card_univ, Fintype.card_bool]
  have hkm : (Finset.univ.filter (fun i => v i = 1)).card ≤ m := by
    have := Finset.card_le_univ (Finset.univ.filter (fun i => v i = 1))
    rwa [Fintype.card_fin] at this
  have hcompl : (Finset.univ.filter (fun i => v i = 1))ᶜ.card =
      m - (Finset.univ.filter (fun i => v i = 1)).card := by
    rw [Finset.card_compl, Fintype.card_fin]
  rw [hcompl] at hcard
  have h3 : 3 ≤ M.ncard := H.cnt.1
  have h9 : M.ncard ≤ 9 := H.cnt.2
  rcases count_not_mem hm5 hm7 hkm with h | h <;> omega

theorem gen_restrict :
    pSpan (restrictFamily (famA R A) (pSpan (famA R A))) = ⊤ := by
  have hmap : (pSpan (restrictFamily (famA R A) (pSpan (famA R A)))).map
      (pSpan (famA R A)).subtype = pSpan (famA R A) := by
    refine le_antisymm (Subgroup.map_subtype_le _) (pSpan_le fun L hL => ?_)
    calc L = (L.subgroupOf (pSpan (famA R A))).map (pSpan (famA R A)).subtype :=
          (Subgroup.map_subgroupOf_eq_of_le (le_pSpan hL)).symm
      _ ≤ _ := Subgroup.map_mono
          (le_pSpan (P := restrictFamily (famA R A) (pSpan (famA R A))) ⟨L, hL, le_pSpan hL, rfl⟩)
  apply Subgroup.map_injective (pSpan (famA R A)).subtype_injective
  rw [hmap, ← MonoidHom.range_eq_map, Subgroup.range_subtype]

theorem restrict_eq :
    restrictFamily (Om R) (xA R A) = restrictFamily (famA R A) (pSpan (famA R A)) := by
  ext L
  constructor
  · rintro ⟨J, hJ, hJX, rfl⟩
    exact ⟨J, ⟨hJ, hJX.trans (xA_le R A)⟩, hJX, rfl⟩
  · rintro ⟨J, hJ, hJX, rfl⟩
    exact ⟨J, hJ.1, hJX, rfl⟩

theorem nonempty_aeIdentOn (hT : Thm4RTwinBelow 3 n)
    (I : AEIdentOn (SectionThmD.secClass (xA R A) (conjSub b (tightCore R))) 7 AE.e64Sets
      AE.e64Sub) :
    Nonempty (AEIdentOn (famA R A) 7 AE.e64Sets AE.e64Sub) := by
  have hfam : SectionThmD.secClass (xA R A) (conjSub b (tightCore R)) =
      quotFamZ (classicalInvolutionOddCore ↥(xA R A)) (restrictFamily (Om R) (xA R A)) := by
    ext L
    constructor
    · intro hL
      obtain ⟨x, rfl⟩ := SectionThmD.mem_secClass_iff.mp hL
      exact ⟨_, ⟨_, H.hypOmega.conjInvariant _ _ H.mem_K1, H.conj_le_X H.K1_le_X x.2, rfl⟩, rfl⟩
    · rintro ⟨_, ⟨J, hJ, hJX, rfl⟩, rfl⟩
      exact H.mem_secClass_of hT hJ hJX
  have hgen : pSpan (restrictFamily (Om R) (xA R A)) = ⊤ := by
    rw [H.restrict_eq]
    exact H.gen_restrict
  have hO : ThmDHypO 3 (restrictFamily (Om R) (xA R A)) := by
    refine ⟨hypOmegaGen_restrict H.hypOmega (xA R A), ?_, ?_, ?_, hgen, ?_⟩
    · rintro _ ⟨L, hL, -, rfl⟩
      exact (H.two L hL).comap_subtype
    · rintro _ ⟨L, hL, hLX, rfl⟩
      rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe hLX).toEquiv, H.card_of_mem hL]
      norm_num
    · rintro _ ⟨L, hL, hLX, rfl⟩
      exact aEmpty_restrictFamily H.hypOmega H.two subset_rfl hLX (H.aEmpty hL)
    · rintro _ ⟨L, hL, hLX, rfl⟩ u hu
      have hu' : IsUniqueInvolution L (u : Y) := isUniqueInvolution_of_subgroupOf hu hLX
      refine ⟨A.subgroupOf (xA R A), ⟨fun v hv g => ?_⟩, H.isPGroup_A.comap_subtype,
        Subgroup.mem_subgroupOf.mpr (H.zA hT hL hLX hu')⟩
      exact Subgroup.mem_subgroupOf.mpr (H.normA g g.2 v (Subgroup.mem_subgroupOf.mp hv))
  have hZK : ∀ K ∈ restrictFamily (Om R) (xA R A),
      classicalInvolutionOddCore ↥(xA R A) ⊓ K = ⊥ := by
    rintro _ ⟨L, hL, -, rfl⟩
    exact oddCore_inf_eq_bot (H.two L hL).comap_subtype
  have I₁ := AEIdentOn.ofQuotZ hO (H.oddCore_le_center hT) hZK (AEIdentOn.ofEq hfam I)
  exact ⟨AEIdentOn.ofRestrict H.gen_restrict (fun L hL => le_pSpan hL)
    (AEIdentOn.ofEq H.restrict_eq I₁)⟩

theorem exists_nu
    (hT : Thm4RTwinBelow 3 n)
    (J : AEIdentOn (famA R A) 7 AE.e64Sets AE.e64Sub) :
    ∃ ν : ↥(xA R A) →* ↥Solomon73.Yamaki.N0, Function.Surjective ν ∧ Nat.card ν.ker ≤ 2 ∧
      ν.ker ≤ Subgroup.center ↥(xA R A) := by
  have hP2 : ∀ L ∈ restrictFamily (famA R A) (pSpan (famA R A)), IsPGroup 2 L := by
    rintro _ ⟨L, hL, -, rfl⟩
    exact (H.two L hL.1).comap_subtype
  have hOX : classicalInvolutionOddCore ↥(xA R A) = ⊥ :=
    oddCore_eq_bot_of_e64 hP2 H.gen_restrict (H.oddCore_le_center hT) J.φ J.range_eq J.ker_le
  have hk : IsPGroup 2 J.φ.ker := (Generic.isPGroup_center_of_corefree hOX).to_le J.ker_le
  have HE : E64Ker.Hyp J.φ (restrictFamily (famA R A) (pSpan (famA R A))) := by
    refine ⟨J.range_eq, ?_, ?_, ?_, ?_, ?_⟩
    · rintro _ ⟨L, hL, hLX, rfl⟩ x
      rw [Generic.conjSub_subgroupOf]
      exact ⟨_, conjSub_mem_famA (xA_le R A x.2) hL, H.conj_le_X hLX x.2, rfl⟩
    · rintro _ ⟨L, hL, hLX, rfl⟩
      rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe hLX).toEquiv, H.card_of_mem hL.1]
    · rintro _ ⟨L, hL, -, rfl⟩
      exact J.label L hL
    · intro α hα h c
      obtain ⟨L, hL, hlab⟩ := J.label_surj α hα h c
      exact ⟨_, ⟨L, hL, le_pSpan hL, rfl⟩, hlab⟩
    · rintro _ ⟨L, hL, hLX, rfl⟩ _ ⟨L', hL', hL'X, rfl⟩ heq
      obtain ⟨α, -, h, c, hlab⟩ := J.label L hL
      rw [TL4.eq_of_map_le_memBar H.hypOmega H.two (by norm_num) J.φ hk hL.1 hL'.1 hLX hL'X hlab
        heq.le]
  obtain ⟨F⟩ := E64Ker.Lab.exists_lab HE
  have hn0 : F.n0 ∈ J.φ.ker := F.n0_mem_ker HE
  have hn0c : F.n0 ∈ Subgroup.center ↥(xA R A) := J.ker_le hn0
  have hbound := E64Ker.card_le_of_enum F.gen (F.closure_gen_eq_top HE H.gen_restrict) hn0c
    (F.eval_rels HE) (F.partner_mem_zpowers hn0c) (U := F.K1)
    (by rw [F.gen_zero]; exact F.a_mem) (by rw [F.gen_one]; exact F.b_mem)
    (by rw [HE.ord F.K1 F.mem_Q])
  have hrange : 10752 ≤ Nat.card J.φ.range := by
    rw [J.range_eq]
    exact E64Ker.le_card_e64Sub
  have hkereq : J.φ.ker = Subgroup.zpowers F.n0 := E64Ker.ker_eq_zpowers J.φ hrange hn0 hbound
  have hn0sq : F.n0 * F.n0 = 1 := by
    have hz1 := (F.isUniqueInvolution_K1 HE).sq
    obtain ⟨j, hj⟩ : ∃ j, F.n0 = F.z1⁻¹ * F.zj j := ⟨_, rfl⟩
    have hzj := (F.isUniqueInvolution_L HE j).sq
    have hc := Subgroup.mem_center_iff.mp hn0c
    have hzjn : F.zj j = F.z1 * F.n0 := by
      rw [hj]
      group
    rw [hzjn] at hzj
    calc F.n0 * F.n0 = (F.z1 * F.z1) * (F.n0 * F.n0) := by rw [hz1, one_mul]
      _ = F.z1 * (F.z1 * F.n0) * F.n0 := by group
      _ = F.z1 * (F.n0 * F.z1) * F.n0 := by rw [hc F.z1]
      _ = F.z1 * F.n0 * (F.z1 * F.n0) := by group
      _ = 1 := hzj
  have hcard2 : Nat.card J.φ.ker ≤ 2 := by
    rw [hkereq, Nat.card_zpowers]
    exact Nat.le_of_dvd (by norm_num) (orderOf_dvd_of_pow_eq_one (by rw [pow_two]; exact hn0sq))
  obtain ⟨e₀⟩ := Sp62Rec.nonempty_e64Sub_mulEquiv_N0
  let φ' : ↥(xA R A) →* ↥AE.e64Sub :=
    J.φ.codRestrict AE.e64Sub fun x => by
      have h : J.φ x ∈ J.φ.range := ⟨x, rfl⟩
      rwa [J.range_eq] at h
  have hker : (e₀.toMonoidHom.comp φ').ker = J.φ.ker := by
    ext x
    rw [MonoidHom.mem_ker, MonoidHom.mem_ker, MonoidHom.comp_apply, MulEquiv.coe_toMonoidHom,
      MulEquiv.map_eq_one_iff]
    constructor
    · intro h
      exact congrArg Subtype.val h
    · intro h
      exact Subtype.ext h
  refine ⟨e₀.toMonoidHom.comp φ', fun y => ?_, by rw [hker]; exact hcard2,
    by rw [hker]; exact J.ker_le⟩
  have hy : ((e₀.symm y : ↥AE.e64Sub) : AE.AEQ 7) ∈ J.φ.range := by
    rw [J.range_eq]
    exact (e₀.symm y).2
  obtain ⟨x, hx⟩ := hy
  refine ⟨x, ?_⟩
  have : φ' x = e₀.symm y := Subtype.ext hx
  show e₀ (φ' x) = y
  rw [this, MulEquiv.apply_symm_apply]

theorem nu
    (hP : TL4.TightBelowRPlus 3 n) (hT : Thm4RTwinBelow 3 n) :
    ∃ ν : ↥(xA R A) →* ↥Solomon73.Yamaki.N0, Function.Surjective ν ∧ Nat.card ν.ker ≤ 2 ∧
      ν.ker ≤ Subgroup.center ↥(xA R A) := by
  rcases H.thmDConcl hP hT with hsing | ⟨W', hW'⟩ | ⟨E', hE'⟩ | hI64 | ⟨m, hm5, hIm⟩ | hI29
  · exact (H.false_of_single hT hsing).elim
  · exact (H.false_of_wSet hT hW').elim
  · exact (H.false_of_e8 hT hE').elim
  · obtain ⟨I⟩ := hI64
    obtain ⟨J⟩ := H.nonempty_aeIdentOn hT I
    exact H.exists_nu hT J
  · obtain ⟨I⟩ := hIm
    by_cases hm7 : m ≤ 7
    · exact (H.false_of_ae_le7 hT hm5 hm7 I).elim
    · exact (H.false_of_ae_ge8 hT (by omega) I).elim
  · obtain ⟨I⟩ := hI29
    exact (H.false_of_e29 hT I).elim

end Hyp

end Cert

section Derive

variable {n : ℕ} {Y : Type} [Group Y] [Finite Y] {R : Subgroup Y} {S : Sylow 2 R} {t : Y}
  {K' W : Subgroup Y} {u e g : Y}

theorem mem_normalizer_of_conjSub_eq {K : Subgroup Y} {x : Y} (h : conjSub x K = K) :
    x ∈ Subgroup.normalizer (K : Set Y) := by
  rw [Subgroup.mem_normalizer_iff]
  intro y
  constructor
  · intro hy
    have := conj_mem_conjSub (n := x) hy
    rwa [h] at this
  · intro hy
    rw [← h, mem_conjSub_iff] at hy
    simpa [mul_assoc] using hy

theorem oddCoreIn_E_eq_bot {E : Subgroup Y} (hEC : E ≤ Subgroup.centralizer ({e} : Set Y))
    (hEn : ∀ g ∈ Subgroup.centralizer ({e} : Set Y), E.map (MulAut.conj g).toMonoidHom = E)
    (hOe : oddCoreIn (Subgroup.centralizer ({e} : Set Y)) = ⊥) : oddCoreIn E = ⊥ := by
  have hN : Subgroup.centralizer ({e} : Set Y) ≤ Subgroup.normalizer (E : Set Y) :=
    fun g hg => mem_normalizer_of_conjSub_eq (hEn g hg)
  have hsub : IsSubnormal E (Subgroup.centralizer ({e} : Set Y)) :=
    isSubnormal_of_normal_subgroupOf hEC ((Subgroup.normal_subgroupOf_iff_le_normalizer hEC).mpr hN)
  have := oddCoreIn_le_of_isSubnormal hsub
  rw [hOe] at this
  exact le_bot_iff.mp this

theorem card_le_512 {B V : Subgroup Y} (hB : Nat.card B = 23040) (hVB : V ≤ B)
    (hV2 : IsPGroup 2 V) : Nat.card V ≤ 512 := by
  obtain ⟨j, hj⟩ := IsPGroup.iff_card.mp hV2
  have hdvd : 2 ^ j ∣ 2 ^ 9 * 45 := by
    rw [← hj, show (2 : ℕ) ^ 9 * 45 = 23040 by norm_num, ← hB]
    exact Subgroup.card_dvd_of_le hVB
  have hco : Nat.Coprime (2 ^ j) 45 := Nat.Coprime.pow_left j (by norm_num)
  have h1 : 2 ^ j ∣ 2 ^ 9 := hco.dvd_of_dvd_mul_right hdvd
  rw [hj]
  exact Nat.le_of_dvd (by norm_num) h1

theorem isSylow2In_of_card_512 {B V : Subgroup Y} (hB : Nat.card B = 23040) (hVB : V ≤ B)
    (hV2 : IsPGroup 2 V) (hV : Nat.card V = 512) : IsSylow2In V B :=
  ⟨hVB, hV2, fun V' hV'B hV'2 hle => (Subgroup.eq_of_le_of_card_ge hle
    (by rw [hV]; exact card_le_512 hB hV'B hV'2)).symm⟩

theorem exists_b (hc : P23Cfg n Y R S t K' W u e g)
    (h2 : ∀ J ∈ Om R, IsPGroup 2 J) {Z : Subgroup Y}
    (hSix : I1Six t e (rLayer (Om R) e) (Z ⊔ rLayer (Om R) e))
    (hOe : oddCoreIn (Subgroup.centralizer ({e} : Set Y)) = ⊥) {T : Subgroup Y}
    (hTB : T ≤ Z ⊔ rLayer (Om R) e) (hT512 : Nat.card T = 512) :
    ∃ b ∈ Z ⊔ rLayer (Om R) e, conjSub b (tightCore R) ≤ T ∧ conjSub b K' ≤ T ∧
      b * t * b⁻¹ ∈ T ∧ (∀ x ∈ T, b * t * b⁻¹ * x = x * (b * t * b⁻¹)) ∧
      IsSylow2In T (Z ⊔ rLayer (Om R) e) ∧ Nat.card ↥(Z ⊔ rLayer (Om R) e) = 23040 := by
  classical
  set E := rLayer (Om R) e with hEdef
  set B := Z ⊔ E with hBdef
  have hC := CoreData.of_S hc.std.perp.core
  have hΩ : HypOmegaGen (Om R) := hC.hyp
  have hK : tightCore R ∈ Om R := CoreAssembly.mem_conjClass_self _
  have hz : IsUniqueInvolution (tightCore R) t := Inner.isUniqueInvolution_core hC.datum
  have hz' : IsUniqueInvolution K' t := isUniqueInvolution_of_mem_twinSet hz hc.std.hK'
  have hOE : oddCoreIn E = ⊥ := oddCoreIn_E_eq_bot (TwinPerpV3.rLayer_le_centralizer _ _)
    hSix.E_normal hOe
  obtain ⟨φ, hφs, hφk, -, -, hodd⟩ := hSix.hat
  have hφi : Function.Injective φ := by
    rw [← MonoidHom.ker_eq_bot_iff, hφk, hOE, Subgroup.bot_subgroupOf]
  have hBcard : Nat.card B = 23040 := by
    rw [← Solomon73.Yamaki.card_Hhat]
    exact Nat.card_congr (Equiv.ofBijective φ ⟨hφi, hφs⟩)
  set t₀ : ↥B := ⟨t, hSix.z_mem⟩ with ht₀
  have hcomap : (Subgroup.centralizer ({t} : Set Y)).subgroupOf B =
      (Subgroup.centralizer ({φ t₀} : Set ↥Solomon73.Yamaki.Hhat)).comap φ := by
    ext x
    rw [Subgroup.mem_subgroupOf, Subgroup.mem_comap, Subgroup.mem_centralizer_singleton_iff,
      Subgroup.mem_centralizer_singleton_iff, ← map_mul, ← map_mul, hφi.eq_iff]
    constructor
    · intro h
      exact Subtype.ext h
    · intro h
      exact congrArg Subtype.val h
  have hoddB : Odd ((Subgroup.centralizer ({t} : Set Y)).relIndex B) := by
    rw [Subgroup.relIndex, hcomap, Subgroup.index_comap_of_surjective _ hφs]
    exact hodd
  have hKe : tightCore R ≤ Subgroup.centralizer ({e} : Set Y) := by
    obtain ⟨R₁, -, -, -, hR₁, -, hRD, -⟩ := e_decomp hc
    have heq : tightCore R = R₁ := hR₁.2.2 (tightCore R) le_rfl (h2 _ hK) hR₁.1
    rw [heq]
    exact hRD.2.trans (normalizer_le_centralizer_e hc.data)
  have hK'e : K' ≤ Subgroup.centralizer ({e} : Set Y) := by
    obtain ⟨-, R₁', -, -, -, hR₁', -, hR'D, -⟩ := e_decomp hc
    have heq : K' = R₁' := hR₁'.2.2 K' le_rfl (h2 _ hc.std.hK'.1) hR₁'.1
    rw [heq]
    exact hR'D.2.trans (normalizer_le_centralizer_e hc.data)
  have hKE : tightCore R ≤ E :=
    C22G.le_rLayer_of_le_centralizer (TC.mem_RSet_of_isPGroup hK (h2 _ hK)) hKe
  have hK'E : K' ≤ E :=
    C22G.le_rLayer_of_le_centralizer (TC.mem_RSet_of_isPGroup hc.std.hK'.1 (h2 _ hc.std.hK'.1)) hK'e
  have hct : ∀ {L : Subgroup Y}, IsUniqueInvolution L t →
      L ≤ Subgroup.centralizer ({t} : Set Y) := by
    intro L hL x hx
    rw [Subgroup.mem_centralizer_singleton_iff]
    have := hL.conj_eq (conjSub_eq_self_of_mem hx)
    calc x * t = x * t * x⁻¹ * x := by group
      _ = t * x := by rw [this]
  have hcomm := OddQuot.commutes_of_twin_pgroup hΩ h2 hK hc.std.hK'.1 hc.std.hne.symm hz hz'
  have hKK2 : IsPGroup 2 ↥(tightCore R ⊔ K') :=
    (h2 _ hK).to_sup_of_normal_right' (h2 _ hc.std.hK'.1)
      (le_normalizer_of_comm fun x hx y hy => hcomm x hx y hy)
  set H₀ := Subgroup.centralizer ({t} : Set Y) ⊓ B with hH₀
  have hKKH : tightCore R ⊔ K' ≤ H₀ :=
    sup_le (le_inf (hct hz) (hKE.trans le_sup_right)) (le_inf (hct hz') (hK'E.trans le_sup_right))
  obtain ⟨P, hP, hKKP⟩ := IsSylow2In.exists_ge hKK2 hKKH
  have hPB : P ≤ B := hP.1.trans inf_le_right
  have hPodd : Odd (P.relIndex B) := by
    have hPH : Odd (P.relIndex H₀) := by
      have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
      let Ps : Sylow 2 ↥H₀ :=
        { toSubgroup := P.subgroupOf H₀
          isPGroup' := hP.2.1.comap_subtype
          is_maximal' := by
            intro Q hQ hle
            have hVQ : P ≤ Q.map H₀.subtype := by
              rw [← Subgroup.map_subgroupOf_eq_of_le hP.1]
              exact Subgroup.map_mono hle
            have := hP.2.2 (Q.map H₀.subtype) (Subgroup.map_subtype_le _) (hQ.map _) hVQ
            rw [← Subgroup.comap_map_eq_self_of_injective H₀.subtype_injective Q, this]
            rfl }
      have := Ps.not_dvd_index
      exact Nat.odd_iff.mpr (Nat.two_dvd_ne_zero.mp this)
    rw [← Subgroup.relIndex_mul_relIndex P H₀ B hP.1 inf_le_right, hH₀,
      Subgroup.inf_relIndex_right]
    exact hPH.mul hoddB
  have hPcard : Nat.card P = 512 := by
    have h1 := Subgroup.relIndex_mul_card P B
    rw [inf_eq_left.mpr hPB, hBcard] at h1
    have hle := card_le_512 hBcard hPB hP.2.1
    obtain ⟨k, hk⟩ := IsPGroup.iff_card.mp hP.2.1
    have hdvd : 2 ^ 9 ∣ Nat.card P := by
      have h3 : 2 ^ 9 ∣ P.relIndex B * Nat.card P := by rw [h1]; norm_num
      have hco : Nat.Coprime (2 ^ 9) (P.relIndex B) :=
        Nat.Coprime.pow_left 9 (Nat.coprime_two_left.mpr hPodd)
      exact hco.dvd_of_dvd_mul_left h3
    have := Nat.le_of_dvd (Nat.card_pos) hdvd
    omega
  have hPs : IsSylow2In P B := isSylow2In_of_card_512 hBcard hPB hP.2.1 hPcard
  have hTs : IsSylow2In T B :=
    isSylow2In_of_card_512 hBcard hTB (IsPGroup.of_card (n := 9) (by rw [hT512]; norm_num))
      hT512
  obtain ⟨b, hbB, hbP⟩ := Asc77.Thompson.exists_conj_of_isSylow2In hPs hTs
  have hPt : P ≤ Subgroup.centralizer ({t} : Set Y) := hP.1.trans inf_le_left
  refine ⟨b, hbB, ?_, ?_, ?_, ?_, hTs, hBcard⟩
  · rw [← hbP]
    exact conjSub_mono (le_sup_left.trans hKKP)
  · rw [← hbP]
    exact conjSub_mono (le_sup_right.trans hKKP)
  · rw [← hbP]
    exact conj_mem_conjSub (hKKP (Subgroup.mem_sup_left hz.mem))
  · intro x hx
    rw [← hbP, mem_conjSub_iff] at hx
    have h1 := Subgroup.mem_centralizer_singleton_iff.mp (hPt hx)
    calc b * t * b⁻¹ * x = b * (t * (b⁻¹ * x * b)) * b⁻¹ := by group
      _ = b * ((b⁻¹ * x * b) * t) * b⁻¹ := by rw [h1]
      _ = x * (b * t * b⁻¹) := by group

end Derive

end ZX

section Main

variable {n : ℕ}

theorem p23E8ZXStrong_of_leaves
    (hE : TwinThmEW.ThmEQ8) (hT : Thm4RTwinBelow 3 n) (hα : P23Alpha n)
    (hN : P23E8ZNormT n) (hW : P23E8ZXW n) (hME : P23E8ZXE n) : P23E8ZXStrong n := by
  intro hcit hP Y _ _ R S t K' W u e g hc hno hZ hA6 Z hI hSix hOe T A hTB hT512 hAT hA64 huniq
  have hα1 := p23E8ZAlpha_of_normT hE hT hα hN hcit hP hc hno hZ hA6
  have h2 := p23E8Z_members_isPGroup_of_alpha hE hT hcit hP hc hZ hα1
  obtain ⟨b, hbB, hK1T, hK1'T, htT, htc, hTs, -⟩ := ZX.exists_b hc h2 hSix hOe hTB hT512
  have hTN := ZX.le_normalizer_of_unique hAT hA64 huniq
  have hBe : Z ⊔ rLayer (Om R) e ≤ Subgroup.centralizer ({e} : Set Y) := hSix.B_le
  have heB : e ∈ Z ⊔ rLayer (Om R) e := hSix.E_le_B hSix.e_mem
  have he2 : IsPGroup 2 (Subgroup.zpowers e) :=
    ExactLayer.isPGroup_zpowers_of_sq_eq_one hc.data.he2
  have hTe : T ≤ Subgroup.normalizer ((Subgroup.zpowers e : Subgroup Y) : Set Y) := by
    intro x hx
    apply Subgroup.centralizer_le_normalizer
    rw [Subgroup.mem_centralizer_iff]
    intro y hy
    obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.mp hy
    have hxe := Subgroup.mem_centralizer_singleton_iff.mp (hBe (hTB hx))
    exact ((Commute.zpow_left (show Commute e x from hxe.symm) k)).eq
  have heT : e ∈ T := by
    have hsup := hTs.2.2 (T ⊔ Subgroup.zpowers e)
      (sup_le hTB (Subgroup.zpowers_le.mpr heB)) (hTs.2.1.to_sup_of_normal_right' he2 hTe)
      le_sup_left
    rw [← hsup]
    exact Subgroup.mem_sup_right (Subgroup.mem_zpowers e)
  have hecen : ∀ x ∈ T, e * x = x * e := fun x hx =>
    (Subgroup.mem_centralizer_singleton_iff.mp (hBe (hTB hx))).symm
  have ht1sq : b * t * b⁻¹ * (b * t * b⁻¹) = 1 := by
    have := (Inner.isUniqueInvolution_core (CoreData.of_S hc.std.perp.core).datum).sq
    calc b * t * b⁻¹ * (b * t * b⁻¹) = b * (t * t) * b⁻¹ := by group
      _ = 1 := by rw [this]; group
  have H : ZX.Hyp n Y R S t K' W u e g A b :=
    { cfg := hc
      two := h2
      e64 := hA64
      K_le := hK1T.trans hTN
      K'_le := hK1'T.trans hTN
      tA := ZX.mem_of_central hAT hA64 huniq htT ht1sq htc
      eA := ZX.mem_of_central hAT hA64 huniq heT hc.data.he2 hecen
      bC := hBe hbB
      w := hW hcit hP Y R S t K' W u e g hc hno hZ hA6 Z hI hSix hOe T A hTB hT512 hAT hA64 huniq
      cnt := hME hcit hP Y R S t K' W u e g hc hno hZ hA6 Z hI hSix hOe T A hTB hT512 hAT hA64
        huniq }
  exact ⟨ZX.xA R A, ZX.xA_le R A, fun _ hg => ZX.conjSub_xA hg, H.nu hP hT⟩

end Main

end CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinPerp23
