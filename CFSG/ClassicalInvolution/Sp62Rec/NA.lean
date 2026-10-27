module

public import CFSG.ClassicalInvolution.Sp62Rec.NAInit
public import CFSG.ClassicalInvolution.Sp62Rec.NANorm
public import CFSG.ClassicalInvolution.Sp62Rec.NAOrbits
public import CFSG.ClassicalInvolution.Sp62Rec.NAOut
public import CFSG.ClassicalInvolution.Sp62Rec.CEBasic

public section

namespace CFSG.ClassicalInvolution.Sp62Rec

open CFSG.ClassicalInvolution.Solomon73 CFSG.ClassicalInvolution.Solomon73.Yamaki
  CFSG.ClassicalInvolution.Balance CFSG.Open

variable {G : Type} [Group G]
  [Finite G] {z e : G} {E B : Subgroup G} {T : Sylow 2 G} {A X : Subgroup G}
  {A0 : Subgroup (StatedSp 3 (ZMod 2))} {rho : StatedSp 3 (ZMod 2)}

private theorem mem_iff_of_map_eq_na {M N : Type} [Group M] [Group N] {H P : Subgroup M}
    {K S : Subgroup N} (φ : ↥H ≃* ↥K)
    (hφ : (P.subgroupOf H).map φ.toMonoidHom = S.subgroupOf K) (x : M) (hx : x ∈ H) :
    x ∈ P ↔ ((φ ⟨x, hx⟩ : ↥K) : N) ∈ S := by
  constructor
  · intro hxP
    have h1 : φ ⟨x, hx⟩ ∈ (P.subgroupOf H).map φ.toMonoidHom :=
      Subgroup.mem_map_of_mem _ (Subgroup.mem_subgroupOf.mpr hxP)
    rw [hφ] at h1
    exact Subgroup.mem_subgroupOf.mp h1
  · intro hS
    have h1 : φ ⟨x, hx⟩ ∈ S.subgroupOf K := Subgroup.mem_subgroupOf.mpr hS
    rw [← hφ] at h1
    obtain ⟨y, hy, hyeq⟩ := Subgroup.mem_map.mp h1
    have hyx : y = ⟨x, hx⟩ := φ.injective hyeq
    have hy' : (y : M) ∈ P := Subgroup.mem_subgroupOf.mp hy
    rw [hyx] at hy'
    exact hy'

theorem E8ZPkg.na (P : E8ZPkg z e E B T A X)
    (θ : ↥(Subgroup.centralizer ({e} : Set G)) ≃* ↥Hhat)
    (hθe : θ ⟨e, Subgroup.mem_centralizer_singleton_iff.2 rfl⟩ = ⟨alpha, alpha_mem_Hhat⟩)
    (hθT : ((T : Subgroup G).subgroupOf (Subgroup.centralizer ({e} : Set G))).map
      θ.toMonoidHom = S0.subgroupOf Hhat)
    (hθA : (A.subgroupOf (Subgroup.centralizer ({e} : Set G))).map θ.toMonoidHom =
      A0.subgroupOf Hhat)
    (hαA0 : alpha ∈ A0) (hpi12A0 : pi12 ∈ A0) (hA0S0 : A0 ≤ S0) (hcardA0 : Nat.card A0 = 64)
    (hCA0 : ∀ x ∈ Hhat, (∀ a ∈ A0, x * a = a * x) → x ∈ A0)
    (hA0N : ∀ Q : Subgroup (StatedSp 3 (ZMod 2)), Q ≤ N0 →
      (∀ n ∈ N0, ∀ x ∈ Q, n * x * n⁻¹ ∈ Q) → IsPGroup 2 Q → Q ≤ A0)
    (hA0 : ∀ A' : Subgroup (StatedSp 3 (ZMod 2)), A' ≤ S0 → IsE64 A' → A' = A0)
    (hN0A0 : N0 ≤ Subgroup.normalizer (A0 : Set (StatedSp 3 (ZMod 2))))
    (hNX0 : ∀ x ∈ Hhat, x ∈ Subgroup.normalizer (A0 : Set (StatedSp 3 (ZMod 2))) → x ∈ X0)
    (hαX0 : ∀ n ∈ N0, n * alpha = alpha * n → n ∈ X0)
    (hrhoA0 : rho ∈ A0)
    (hcover : ∀ a ∈ A0, a ≠ 1 → a ∈ orbIn N0 alpha ∨ a ∈ orbIn N0 pi12 ∨ a ∈ orbIn N0 pi3 ∨
      a ∈ orbIn N0 rho)
    (horbα : (orbIn N0 alpha).ncard = 7) (horbρ : (orbIn N0 rho).ncard = 28)
    (hD : Nat.card (Subgroup.closure (orbIn N0 pi12)) = 8)
    (hfpf : ∃ x ∈ N0, x ^ 7 = 1 ∧ x ≠ 1 ∧ ∀ a ∈ A0, a * x = x * a → a = 1)
    (hρ : ∃ ρ : ↥N0 →* GL (Fin 3) (ZMod 2), Function.Surjective ρ ∧ ρ.ker = A0.subgroupOf N0)
    (hS0 : Nat.card S0 = 512) (hN0 : Nat.card N0 = 10752) (hX0 : Nat.card X0 = 1536)
    (hα : Hhat ≤ Subgroup.centralizer ({alpha} : Set (StatedSp 3 (ZMod 2)))) :
    Subgroup.centralizer (A : Set G) = A ∧ AutL32 A ∧
      (∃ x ∈ Subgroup.normalizer (A : Set G), Odd (orderOf x) ∧ ∀ a ∈ A, a * x = x * a → a = 1) ∧
      (∃ n ∈ Subgroup.normalizer (A : Set G), n ∉ Subgroup.centralizer ({e} : Set G)) ∧
      ∃ ν : ↥(Subgroup.normalizer (A : Set G)) ≃* ↥N0,
        ((T : Subgroup G).subgroupOf (Subgroup.normalizer (A : Set G))).map ν.toMonoidHom =
          S0.subgroupOf N0 ∧
        (A.subgroupOf (Subgroup.normalizer (A : Set G))).map ν.toMonoidHom = A0.subgroupOf N0 ∧
        (∀ c (h1 : c ∈ Subgroup.normalizer (A : Set G))
            (h2 : c ∈ Subgroup.centralizer ({e} : Set G)),
          c ∈ (T : Subgroup G) → (∀ t ∈ (T : Subgroup G), c * t = t * c) →
            ((ν ⟨c, h1⟩ : ↥N0) : StatedSp 3 (ZMod 2)) =
              ((θ ⟨c, h2⟩ : ↥Hhat) : StatedSp 3 (ZMod 2))) ∧
        (∀ x (hx : x ∈ Subgroup.centralizer ({e} : Set G)),
          x ∈ Subgroup.normalizer (A : Set G) ↔
            ((θ ⟨x, hx⟩ : ↥Hhat) : StatedSp 3 (ZMod 2)) ∈ X0) ∧
        (∀ x (hx : x ∈ Subgroup.normalizer (A : Set G)),
          x ∈ Subgroup.centralizer ({e} : Set G) ↔
            ((ν ⟨x, hx⟩ : ↥N0) : StatedSp 3 (ZMod 2)) ∈ X0) := by
  have hTCe : (T : Subgroup G) ≤ Subgroup.centralizer ({e} : Set G) := P.T_le.trans P.B_le
  have hACe : A ≤ Subgroup.centralizer ({e} : Set G) := P.A_le.trans hTCe
  have hA0H : A0 ≤ Hhat := hA0S0.trans S0_le_Hhat
  have hX0N : X0 ≤ Subgroup.normalizer (A0 : Set (StatedSp 3 (ZMod 2))) :=
    X0_le_N0.trans hN0A0
  have heCe : e ∈ Subgroup.centralizer ({e} : Set G) :=
    Subgroup.mem_centralizer_singleton_iff.2 rfl
  obtain ⟨heA, hCA⟩ := P.centralizer_A_eq_of_le θ hθe hθA hαA0 hA0H hCA0
  have hθT' : ∀ x (hx : x ∈ Subgroup.centralizer ({e} : Set G)),
      x ∈ (T : Subgroup G) ↔ ((θ ⟨x, hx⟩ : ↥Hhat) : StatedSp 3 (ZMod 2)) ∈ S0 :=
    fun x hx => mem_iff_of_map_eq_na θ hθT x hx
  have hTcard : Nat.card (T : Subgroup G) = 512 := by
    have h1 : Nat.card (((T : Subgroup G).subgroupOf (Subgroup.centralizer ({e} : Set G))).map
        θ.toMonoidHom) =
        Nat.card ((T : Subgroup G).subgroupOf (Subgroup.centralizer ({e} : Set G))) :=
      Subgroup.card_map_of_injective (f := θ.toMonoidHom) θ.injective
    rw [hθT, Nat.card_congr (Subgroup.subgroupOfEquivOfLe S0_le_Hhat).toEquiv, hS0,
      Nat.card_congr (Subgroup.subgroupOfEquivOfLe hTCe).toEquiv] at h1
    exact h1.symm
  obtain ⟨hAX, ν₁, hν₁A⟩ := P.exists_nu hCA hTcard hN0 hcardA0 hA0N
  have huniq : ∀ A' : Subgroup G, A' ≤ (T : Subgroup G) → IsE64 A' → A' = A := by
    intro A' hA'T hA'
    have hA'Ce : A' ≤ Subgroup.centralizer ({e} : Set G) := hA'T.trans hTCe
    obtain ⟨ι, hι_apply⟩ : ∃ ι : ↥(Subgroup.centralizer ({e} : Set G)) →* StatedSp 3 (ZMod 2),
        ∀ x, ι x = ((θ x : ↥Hhat) : StatedSp 3 (ZMod 2)) :=
      ⟨Hhat.subtype.comp θ.toMonoidHom, fun x => rfl⟩
    have hι : Function.Injective ι := by
      intro x y hxy
      rw [hι_apply, hι_apply] at hxy
      exact θ.injective (Subtype.ext hxy)
    have hιeq : ι = Hhat.subtype.comp θ.toMonoidHom := MonoidHom.ext hι_apply
    have hDA' : (A'.subgroupOf (Subgroup.centralizer ({e} : Set G))).map ι = A0 := by
      apply hA0 _ ?_ ?_
      · rintro _ ⟨x, hx, rfl⟩
        rw [hι_apply]
        exact (hθT' x x.2).mp (hA'T (Subgroup.mem_subgroupOf.mp hx))
      · refine ⟨?_, ?_, ?_⟩
        · intro a ha b hb
          obtain ⟨x, hx, rfl⟩ := Subgroup.mem_map.mp ha
          obtain ⟨y, hy, rfl⟩ := Subgroup.mem_map.mp hb
          rw [← map_mul, ← map_mul]
          exact congrArg ι (Subtype.ext (hA'.1 _ (Subgroup.mem_subgroupOf.mp hx) _
            (Subgroup.mem_subgroupOf.mp hy)))
        · intro a ha
          obtain ⟨x, hx, rfl⟩ := Subgroup.mem_map.mp ha
          rw [← map_mul]
          have hxx : x * x = 1 := Subtype.ext (hA'.2.1 _ (Subgroup.mem_subgroupOf.mp hx))
          rw [hxx, map_one]
        · rw [Subgroup.card_map_of_injective hι,
            Nat.card_congr (Subgroup.subgroupOfEquivOfLe hA'Ce).toEquiv, hA'.2.2]
    have hDA : (A.subgroupOf (Subgroup.centralizer ({e} : Set G))).map ι = A0 := by
      rw [hιeq, ← Subgroup.map_map, hθA, Subgroup.subgroupOf_map_subtype,
        inf_eq_left.mpr hA0H]
    have hsub : A'.subgroupOf (Subgroup.centralizer ({e} : Set G)) =
        A.subgroupOf (Subgroup.centralizer ({e} : Set G)) :=
      Subgroup.map_injective hι (hDA'.trans hDA.symm)
    calc A' = A' ⊓ Subgroup.centralizer ({e} : Set G) := (inf_eq_left.mpr hA'Ce).symm
      _ = (A'.subgroupOf (Subgroup.centralizer ({e} : Set G))).map
            (Subgroup.centralizer ({e} : Set G)).subtype :=
          (Subgroup.subgroupOf_map_subtype _ _).symm
      _ = (A.subgroupOf (Subgroup.centralizer ({e} : Set G))).map
            (Subgroup.centralizer ({e} : Set G)).subtype := by rw [hsub]
      _ = A ⊓ Subgroup.centralizer ({e} : Set G) := Subgroup.subgroupOf_map_subtype _ _
      _ = A := inf_eq_left.mpr hACe
  obtain ⟨X', ν', hX'N, hTX', hAX', hν'A, hν'T⟩ :=
    exists_conj_nu P.e64 P.X_le hAX P.A_le huniq hTcard ν₁ hν₁A hS0 hN0 hN0A0
  have haut : ∀ f : ↥S0 ≃* ↥S0, ∀ x : ↥S0, (∀ w : ↥S0, x * w = w * x) → f x = x :=
    fun f x hx =>
      mulEquiv_S0_apply_of_mem_center f (Subgroup.mem_center_iff.mpr fun w => (hx w).symm)
  have heT : e ∈ (T : Subgroup G) := P.e_mem_T
  have hecT : ∀ t ∈ (T : Subgroup G), e * t = t * e := fun t ht =>
    Subgroup.mem_centralizer_iff.mp (hTCe ht) e (Set.mem_singleton e)
  have hνe : ((ν' ⟨e, hAX' heA⟩ : ↥N0) : StatedSp 3 (ZMod 2)) = alpha :=
    (agree_on_center θ hTCe hθT ν' hTX' hν'T haut heT hecT).trans (congrArg Subtype.val hθe)
  obtain ⟨y, hyCe, hθy⟩ : ∃ y : G, ∃ hy : y ∈ Subgroup.centralizer ({e} : Set G),
      θ ⟨y, hy⟩ = ⟨pi12, S0_le_Hhat pi12_mem_S0⟩ :=
    ⟨((θ.symm ⟨pi12, S0_le_Hhat pi12_mem_S0⟩ : ↥(Subgroup.centralizer ({e} : Set G))) : G),
      (θ.symm ⟨pi12, S0_le_Hhat pi12_mem_S0⟩).2, θ.apply_symm_apply _⟩
  have hyA : y ∈ A := (mem_iff_of_map_eq_na θ hθA y hyCe).mpr (by
    rw [hθy]
    exact hpi12A0)
  have hyT : y ∈ (T : Subgroup G) := (hθT' y hyCe).mpr (by
    rw [hθy]
    exact pi12_mem_S0)
  have hyZ : ∀ t ∈ (T : Subgroup G), y * t = t * y := by
    intro t ht
    have htS : ((θ ⟨t, hTCe ht⟩ : ↥Hhat) : StatedSp 3 (ZMod 2)) ∈ S0 :=
      (hθT' t (hTCe ht)).mp ht
    have hab : θ (⟨y, hyCe⟩ * ⟨t, hTCe ht⟩) = θ (⟨t, hTCe ht⟩ * ⟨y, hyCe⟩) := by
      rw [map_mul, map_mul, hθy]
      apply Subtype.ext
      exact (commute_pi12 htS).symm
    exact congrArg Subtype.val (θ.injective hab)
  have hνy : ((ν' ⟨y, hAX' hyA⟩ : ↥N0) : StatedSp 3 (ZMod 2)) = pi12 :=
    (agree_on_center θ hTCe hθT ν' hTX' hν'T haut hyT hyZ).trans (congrArg Subtype.val hθy)
  have hsα : (θ.symm ⟨alpha, S0_le_Hhat alpha_mem_S0⟩ : G) = e := by
    have h : θ.symm ⟨alpha, S0_le_Hhat alpha_mem_S0⟩ = ⟨e, heCe⟩ := by
      rw [MulEquiv.symm_apply_eq]
      exact hθe.symm
    exact congrArg Subtype.val h
  have hsπ : (θ.symm ⟨pi12, S0_le_Hhat pi12_mem_S0⟩ : G) = y := by
    have h : θ.symm ⟨pi12, S0_le_Hhat pi12_mem_S0⟩ = ⟨y, hyCe⟩ := by
      rw [MulEquiv.symm_apply_eq]
      exact hθy.symm
    exact congrArg Subtype.val h
  have hsπ3 : (θ.symm ⟨pi3, S0_le_Hhat pi3_mem_S0⟩ : G) = e * y := by
    have hmul : θ (⟨e, heCe⟩ * ⟨y, hyCe⟩) = ⟨pi3, S0_le_Hhat pi3_mem_S0⟩ := by
      rw [map_mul, hθe, hθy]
      exact Subtype.ext rfl
    have h : θ.symm ⟨pi3, S0_le_Hhat pi3_mem_S0⟩ = ⟨e, heCe⟩ * ⟨y, hyCe⟩ := by
      rw [MulEquiv.symm_apply_eq]
      exact hmul.symm
    exact congrArg Subtype.val h
  have hnc1 : ¬ IsConj e y := by
    have h := not_isConj_symm_alpha_pi12 T S0_le_Hhat θ hTCe hθT'
    rwa [hsα, hsπ] at h
  have hnc2 : ¬ IsConj e (e * y) := by
    have h := not_isConj_symm_alpha_pi3 T S0_le_Hhat θ hTCe hθT'
    rwa [hsα, hsπ3] at h
  have hnc3 : ¬ IsConj y (e * y) := by
    have h := not_isConj_symm_pi12_pi3 T S0_le_Hhat θ hTCe hθT'
    rwa [hsπ, hsπ3] at h
  have hrig : ∀ g : G, g * e * g⁻¹ ≠ y ∧ g * e * g⁻¹ ≠ e * y ∧ g * y * g⁻¹ ≠ e * y :=
    fun g => ⟨fun h => hnc1 (isConj_iff.mpr ⟨g, h⟩), fun h => hnc2 (isConj_iff.mpr ⟨g, h⟩),
      fun h => hnc3 (isConj_iff.mpr ⟨g, h⟩)⟩
  have hNA : Subgroup.normalizer (A : Set G) = X' :=
    normalizer_eq_of_nu θ hACe hθA P.e64 heA hCA hX'N hAX' ν' hν'A hνe hyA hνy hrig hcover
      hrhoA0 horbα horbρ hD hX0 hN0 hNX0 hX0N
  subst hNA
  have hcard : Nat.card ↥(Subgroup.normalizer (A : Set G) ⊓ Subgroup.centralizer ({e} : Set G)) <
      Nat.card ↥(Subgroup.normalizer (A : Set G)) := by
    rw [card_normalizer_inf_centralizer θ hACe hθA hA0H hNX0 hX0N, hX0,
      Nat.card_congr ν'.toEquiv, hN0]
    norm_num
  refine ⟨hCA, autL32_of_nu rfl ν' hν'A hCA hρ, exists_fpf_of_nu rfl ν' hν'A hAX' hfpf,
    exists_mem_normalizer_not_mem_centralizer hcard, ν', hν'T, hν'A, ?_, ?_, ?_⟩
  · intro c _ _ hcT hcZ
    exact agree_on_center θ hTCe hθT ν' hTX' hν'T haut hcT hcZ
  · intro x hx
    exact mem_normalizer_iff_theta θ hACe hθA hA0H hNX0 hX0N x hx
  · intro x hx
    exact mem_centralizer_iff_nu ν' (hAX' heA) hνe hαX0 hα x hx

end CFSG.ClassicalInvolution.Sp62Rec
