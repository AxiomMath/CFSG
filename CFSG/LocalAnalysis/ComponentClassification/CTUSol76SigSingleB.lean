module

public import CFSG.LocalAnalysis.ComponentClassification.CTUSol76SigSingleFull
public import CFSG.CGT.T75H.CoprimeFour

public section

namespace CFSG.ComponentClassification.Sol76.Sig

open CFSG Subgroup CFSG.ComponentClassification.FooteLit
  CFSG.ComponentClassification.UnbalancedLayer
open scoped commutatorElement

@[expose] def TwoComponentsQuasisimpleAt (T : Type) [Group T] : Prop :=
  ∀ y : T, orderOf y = 2 → ∀ K : Subgroup T, IsTwoComponentIn K (centralizer ({y} : Set T)) →
    CFSG.IsQuasisimple K

@[expose] def SingleComponentCleanAt (P : (S : Type) → [Group S] → Prop) : Prop :=
  ∀ (T : Type) [Group T] [Finite T], IsSimpleGroup T → P T → ∀ X Y : Subgroup T,
    CFSG.IsQuasisimple X → CFSG.IsQuasisimple Y →
    2 ≤ CFSG.Open.pRank 2 X → 2 ≤ CFSG.Open.pRank 2 Y → ⁅X, Y⁆ = ⊥ →
    (∀ y ∈ Y, orderOf y = 2 → IsTwoComponentIn X (centralizer ({y} : Set T))) →
    (∀ x ∈ X, orderOf x = 2 → IsTwoComponentIn Y (centralizer ({x} : Set T))) →
    False

section Tools

variable {G : Type*} [Group G]

theorem sig_not_isSolvable_of_isQuasisimple {C : Type*} [Group C] (hQ : CFSG.IsQuasisimple C) :
    ¬ Group.IsSolvable C := by
  obtain ⟨hperf, hsimple, -⟩ := hQ
  have : Nontrivial C := (QuotientGroup.mk_surjective (s := Subgroup.center C)).nontrivial
  exact Group.IsPerfect.not_isSolvable C

theorem sigPerfect_le_of_le_sup_normal {P R J : Subgroup G} [P.Normal]
    (hR : Group.IsSolvable R) (hJ : ⁅J, J⁆ = J) (hJPR : J ≤ P ⊔ R) : J ≤ P := by
  set q := QuotientGroup.mk' P
  have hle : J.map q ≤ R.map q :=
    calc J.map q ≤ (P ⊔ R).map q := map_mono hJPR
      _ = R.map q := by
        rw [Subgroup.map_sup, (Subgroup.map_eq_bot_iff P).mpr (QuotientGroup.ker_mk' P).ge,
          bot_sup_eq]
  have : Group.IsSolvable (R.map q) := Group.isSolvable_of_surjective (q.subgroupMap_surjective R)
  have : Group.IsSolvable (J.map q) :=
    Group.isSolvable_of_isSolvable_injective (inclusion_injective hle)
  have : Group.IsPerfect (J.map q) := isPerfect_iff.mpr (by rw [← map_commutator, hJ])
  have hbot : J.map q = ⊥ := by
    by_contra hne
    have : Nontrivial (J.map q) := (nontrivial_iff_ne_bot _).mpr hne
    exact Group.IsPerfect.not_isSolvable (J.map q) inferInstance
  rwa [Subgroup.map_eq_bot_iff, QuotientGroup.ker_mk'] at hbot

theorem sigPerfect_le_of_le_sup {P R J : Subgroup G} (hRP : R ≤ normalizer (P : Set G))
    (hR : Group.IsSolvable R) (hJ : ⁅J, J⁆ = J) (hJPR : J ≤ P ⊔ R) : J ≤ P := by
  set H := P ⊔ R with hH
  have hPH : P ≤ H := le_sup_left
  have hRH : R ≤ H := le_sup_right
  have hJH : J ≤ H := hJPR
  have : (P.subgroupOf H).Normal :=
    (normal_subgroupOf_iff_le_normalizer hPH).mpr (sup_le le_normalizer hRP)
  have hR' : Group.IsSolvable (R.subgroupOf H) :=
    Group.isSolvable_of_isSolvable_injective (f := (subgroupOfEquivOfLe hRH).toMonoidHom)
      (subgroupOfEquivOfLe hRH).injective
  have hJ' : ⁅J.subgroupOf H, J.subgroupOf H⁆ = J.subgroupOf H := by
    apply map_injective H.subtype_injective
    rw [map_commutator, map_subgroupOf_eq_of_le hJH, hJ]
  have hJ'le : J.subgroupOf H ≤ P.subgroupOf H ⊔ R.subgroupOf H := by
    rw [← subgroupOf_sup hPH hRH]
    exact fun g hg => hJPR hg
  have h := sigPerfect_le_of_le_sup_normal hR' hJ' hJ'le
  intro j hj
  exact h (show (⟨j, hJH hj⟩ : H) ∈ J.subgroupOf H from hj)

theorem sig_mul_comm_of_commutator_eq_bot {P S : Subgroup G} (h : ⁅P, S⁆ = ⊥) {p s : G}
    (hp : p ∈ P) (hs : s ∈ S) : p * s = s * p := by
  have h1 := commutator_mem_commutator hp hs
  rw [h, mem_bot, commutatorElement_eq_one_iff_mul_comm] at h1
  exact h1

theorem sig_le_normalizer_of_commutator_eq_bot {P S : Subgroup G} (h : ⁅P, S⁆ = ⊥) :
    S ≤ normalizer (P : Set G) := by
  intro s hs
  rw [mem_normalizer_iff]
  intro p
  constructor
  · intro hp
    rw [← sig_mul_comm_of_commutator_eq_bot h hp hs, mul_inv_cancel_right]
    exact hp
  · intro hp
    have h1 := sig_mul_comm_of_commutator_eq_bot h hp hs
    have h2 : s * p = s * (s * p * s⁻¹) := by rw [← h1, inv_mul_cancel_right]
    rw [mul_left_cancel h2]
    exact hp

end Tools

section B

variable {T : Type} [Group T] [Finite T]

theorem exists_component_le_of_oddFullCoverAt {X : Subgroup T} {y : T}
    (hB : ∀ K : Subgroup T, IsTwoComponentIn K (centralizer ({y} : Set T)) →
      CFSG.IsQuasisimple K)
    (h : OddFullCoverAt X y) :
    ∃ K : Subgroup T, IsTwoComponentIn K (centralizer ({y} : Set T)) ∧ CFSG.IsQuasisimple K ∧
      K ≤ X ∧ K ⊔ oddCoreIn X = X := by
  obtain ⟨P, R, J, hP, hRC, hRn, hRodd, hJ, hJp, hPJR, hJPR, hJcov⟩ := h
  set C := centralizer ({y} : Set T) with hC
  have hPq := hB P hP
  have hPp : ⁅P, P⁆ = P := UnbalancedCorr.commutator_eq_of_isPComponent hP.1 hP.2
  have hPcomp : CFSG.IsComponent (P.subgroupOf C) := by
    refine ⟨?_, ?_⟩
    · exact CatalogueBAlternating.quasisimple_iff_native.mpr (Components.quasisimple_of_equiv
        (subgroupOfEquivOfLe hP.1) (CatalogueBAlternating.quasisimple_iff_native.mp hPq))
    · obtain ⟨-, -, hsub, -, -⟩ := hP.2
      exact hsub
  have hRsolv : Group.IsSolvable R := CFSG.FeitThompson.isSolvable_of_odd_natCard _ hRodd
  rcases CFSG.LocalCores.component_normal_subgroup hPcomp hRn with hle | hcomm
  · exfalso
    have hPR : P ≤ R := fun g hg =>
      hle (show (⟨g, hP.1 hg⟩ : C) ∈ P.subgroupOf C from hg)
    have : Group.IsSolvable P := Group.isSolvable_of_isSolvable_injective (inclusion_injective hPR)
    exact sig_not_isSolvable_of_isQuasisimple hPq this
  · have hPR : ⁅P, R⁆ = ⊥ := by
      have h1 := congrArg (Subgroup.map C.subtype) hcomm
      rwa [Subgroup.map_commutator, map_subgroupOf_eq_of_le hP.1, map_subgroupOf_eq_of_le hRC,
        Subgroup.map_bot] at h1
    have hJP : J ≤ P :=
      sigPerfect_le_of_le_sup (sig_le_normalizer_of_commutator_eq_bot hPR) hRsolv hJp hJPR
    have hJR : ⁅J, R⁆ = ⊥ := eq_bot_iff.mpr ((commutator_mono hJP le_rfl).trans hPR.le)
    have hPJ : P ≤ J :=
      sigPerfect_le_of_le_sup (sig_le_normalizer_of_commutator_eq_bot hJR) hRsolv hPp hPJR
    obtain rfl : J = P := le_antisymm hJP hPJ
    exact ⟨J, hP, hPq, hJ.trans inf_le_left, hJcov⟩

theorem eq_of_isTwoComponentIn_of_sup_eq {H X K₁ K₂ : Subgroup T}
    (hXq : IsQuasisimple (↥X ⧸ pPrimeCore 2 ↥X))
    (h₁ : IsTwoComponentIn K₁ H) (h₂ : IsTwoComponentIn K₂ H) (hK₁X : K₁ ≤ X) (hK₂X : K₂ ≤ X)
    (hc₁ : K₁ ⊔ oddCoreIn X = X) (hc₂ : K₂ ⊔ oddCoreIn X = X) : K₁ = K₂ := by
  by_contra hne
  have hcomm : ⁅K₁, K₂⁆ ≤ oddCoreIn H := commutator_le_oddCoreIn_of_ne h₁ h₂ hne
  set π := QuotientGroup.mk' (pPrimeCore 2 ↥X) with hπ
  have hOX : (oddCoreIn X).subgroupOf X = pPrimeCore 2 ↥X := by
    rw [oddCoreIn, ← comap_subtype, comap_map_eq_self_of_injective X.subtype_injective]
  have himg : ∀ K : Subgroup T, K ≤ X → K ⊔ oddCoreIn X = X → (K.subgroupOf X).map π = ⊤ := by
    intro K hKX hc
    have hOle : oddCoreIn X ≤ X := map_subtype_le _
    have h1 : K.subgroupOf X ⊔ pPrimeCore 2 ↥X = ⊤ := by
      rw [← hOX, ← subgroupOf_sup hKX hOle, hc, subgroupOf_self]
    have h2 := congrArg (Subgroup.map π) h1
    rwa [Subgroup.map_sup, (Subgroup.map_eq_bot_iff _).mpr (QuotientGroup.ker_mk' _).ge,
      sup_bot_eq, Subgroup.map_top_of_surjective π (QuotientGroup.mk'_surjective _)] at h2
  have hle : ⁅K₁.subgroupOf X, K₂.subgroupOf X⁆ ≤ (oddCoreIn H).subgroupOf X := by
    rw [commutator_le]
    intro a ha b hb
    rw [mem_subgroupOf]
    have h' : ((⁅a, b⁆ : X) : T) = ⁅(a : T), (b : T)⁆ := by simp [commutatorElement_def]
    rw [h']
    exact hcomm (commutator_mem_commutator ha hb)
  have hperf : ⁅(⊤ : Subgroup (↥X ⧸ pPrimeCore 2 ↥X)), (⊤ : Subgroup (↥X ⧸ pPrimeCore 2 ↥X))⁆ =
      (⊤ : Subgroup (↥X ⧸ pPrimeCore 2 ↥X)) := by
    have h := hXq.1.commutator_eq_top
    rwa [_root_.commutator_def] at h
  have htop : (⊤ : Subgroup (↥X ⧸ pPrimeCore 2 ↥X)) ≤ ((oddCoreIn H).subgroupOf X).map π := by
    calc (⊤ : Subgroup (↥X ⧸ pPrimeCore 2 ↥X))
        = ⁅(K₁.subgroupOf X).map π, (K₂.subgroupOf X).map π⁆ := by
          rw [himg K₁ hK₁X hc₁, himg K₂ hK₂X hc₂, hperf]
      _ = (⁅K₁.subgroupOf X, K₂.subgroupOf X⁆).map π := (Subgroup.map_commutator _ _ _).symm
      _ ≤ _ := map_mono hle
  have hodd1 : Odd (Nat.card ((oddCoreIn H).subgroupOf X)) := by
    have h1 : Nat.card ((oddCoreIn H).subgroupOf X) = Nat.card (oddCoreIn H ⊓ X : Subgroup T) := by
      rw [← Subgroup.subgroupOf_map_subtype, Subgroup.card_map_of_injective X.subtype_injective]
    rw [h1]
    exact Odd.of_dvd_nat (Nat.coprime_two_left.mp (coprime_card_oddCoreIn H))
      (Subgroup.card_dvd_of_le inf_le_left)
  have hodd : Odd (Nat.card (↥X ⧸ pPrimeCore 2 ↥X)) := by
    have h2 : Odd (Nat.card (((oddCoreIn H).subgroupOf X).map π)) :=
      Odd.of_dvd_nat hodd1 (Subgroup.card_map_dvd _ _)
    rwa [eq_top_iff.mpr htop, Subgroup.card_top] at h2
  exact sig_not_isSolvable_of_isQuasisimple hXq (CFSG.FeitThompson.isSolvable_of_odd_natCard _ hodd)

theorem mem_centralizer_of_commutator_mem_oddCoreIn {X K : Subgroup T} {g : T}
    (hKq : CFSG.IsQuasisimple K) (hKX : K ≤ X) (hgK : g ∈ normalizer (K : Set T))
    (hc : ∀ k ∈ K, ⁅k, g⁆ ∈ oddCoreIn X) : g ∈ centralizer (K : Set T) := by
  set N := (oddCoreIn X).subgroupOf K with hN
  have hNn : N.Normal := by
    refine ⟨fun n hn k => ?_⟩
    rw [hN, mem_subgroupOf] at hn ⊢
    have hkX : (k : T) ∈ normalizer (oddCoreIn X : Set T) :=
      mem_normalizer_iff_map_conj_eq.mpr (map_conj_oddCoreIn (le_normalizer (hKX k.2)))
    simp only [Subgroup.coe_mul, Subgroup.coe_inv]
    exact (mem_normalizer_iff.mp hkX n).mp hn
  have hNZ : N ≤ center ↥K := by
    rcases CFSG.LocalCores.quasisimple_normal_subgroups hKq hNn with htop | hle
    · exfalso
      have hKO : K ≤ oddCoreIn X := fun k hk => by
        have : (⟨k, hk⟩ : K) ∈ N := htop ▸ mem_top _
        exact this
      have hKodd : Odd (Nat.card K) :=
        Odd.of_dvd_nat (Nat.coprime_two_left.mp (coprime_card_oddCoreIn X))
          (Subgroup.card_dvd_of_le hKO)
      exact sig_not_isSolvable_of_isQuasisimple hKq (CFSG.FeitThompson.isSolvable_of_odd_natCard _ hKodd)
    · exact hle
  have hgk : ∀ k ∈ K, g * k * g⁻¹ ∈ K := fun k hk => (mem_normalizer_iff.mp hgK k).mp hk
  have hgk' : ∀ k ∈ K, g⁻¹ * k * g ∈ K := fun k hk => by
    have := (mem_normalizer_iff.mp (inv_mem hgK) k).mp hk
    rwa [inv_inv] at this
  let α : ↥K ≃* ↥K :=
    { toFun := fun k => ⟨g * k * g⁻¹, hgk k k.2⟩
      invFun := fun k => ⟨g⁻¹ * k * g, hgk' k k.2⟩
      left_inv := fun k => Subtype.ext (by simp [mul_assoc])
      right_inv := fun k => Subtype.ext (by simp [mul_assoc])
      map_mul' := fun u v => Subtype.ext (by simp [mul_assoc]) }
  have hα : α = MulEquiv.refl _ := by
    refine GorensteinWalter.perfect_central_automorphism_eq hKq.1 α (MulEquiv.refl _) ?_
    intro k
    have hkg : ⁅(k : T), g⁆ ∈ K := by
      have he : ⁅(k : T), g⁆ = k * (g * (k : T)⁻¹ * g⁻¹) := by rw [commutatorElement_def]; group
      rw [he]
      exact mul_mem k.2 (hgk _ (inv_mem k.2))
    have hmem : (⟨⁅(k : T), g⁆, hkg⟩ : K) ∈ N := hc k k.2
    have hkey : α k * ((MulEquiv.refl ↥K) k)⁻¹ = (⟨⁅(k : T), g⁆, hkg⟩ : K)⁻¹ :=
      Subtype.ext (by simp [α, commutatorElement_def, mul_assoc])
    rw [hkey]
    exact inv_mem (hNZ hmem)
  rw [mem_centralizer_iff]
  intro k hk
  have h1 := congrArg (fun φ : ↥K ≃* ↥K => ((φ ⟨k, hk⟩ : K) : T)) hα
  simp only [MulEquiv.refl_apply, α, MulEquiv.coe_mk, Equiv.coe_fn_mk] at h1
  calc k * g = g * k * g⁻¹ * g := by rw [h1]
    _ = g * k := by group

theorem mem_normalizer_of_isTwoComponentIn_of_sup_eq {X K H : Subgroup T} {g : T}
    (hXq : IsQuasisimple (↥X ⧸ pPrimeCore 2 ↥X))
    (hK : IsTwoComponentIn K H) (hKX : K ≤ X) (hc : K ⊔ oddCoreIn X = X)
    (hgH : g ∈ normalizer (H : Set T)) (hgX : g ∈ normalizer (X : Set T)) :
    g ∈ normalizer (K : Set T) := by
  have hK' : IsTwoComponentIn (K.map (MulAut.conj g).toMonoidHom) H :=
    isTwoComponentIn_map_conj hK hgH
  have hXg : X.map (MulAut.conj g).toMonoidHom = X := mem_normalizer_iff_map_conj_eq.mp hgX
  have hK'X : K.map (MulAut.conj g).toMonoidHom ≤ X := hXg ▸ map_mono hKX
  have hc' : K.map (MulAut.conj g).toMonoidHom ⊔ oddCoreIn X = X := by
    have h1 := congrArg (Subgroup.map (MulAut.conj g).toMonoidHom) hc
    rwa [Subgroup.map_sup, map_conj_oddCoreIn hgX, hXg] at h1
  exact mem_normalizer_iff_map_conj_eq.mpr
    (eq_of_isTwoComponentIn_of_sup_eq hXq hK' hK hK'X hKX hc' hc)

theorem mul_comm_of_mem_oddCoreIn {X : Subgroup T} (hXq : CFSG.IsQuasisimple X) {o x : T}
    (ho : o ∈ oddCoreIn X) (hx : x ∈ X) : o * x = x * o := by
  have hoX : o ∈ X := map_subtype_le _ ho
  have hN : ((oddCoreIn X).subgroupOf X).Normal := by
    rw [oddCoreIn, ← comap_subtype, comap_map_eq_self_of_injective X.subtype_injective]
    infer_instance
  rcases CFSG.LocalCores.quasisimple_normal_subgroups hXq hN with htop | hle
  · exfalso
    have hXO : X ≤ oddCoreIn X := fun k hk => by
      have : (⟨k, hk⟩ : X) ∈ (oddCoreIn X).subgroupOf X := htop ▸ mem_top _
      exact this
    have hXodd : Odd (Nat.card X) :=
      Odd.of_dvd_nat (Nat.coprime_two_left.mp (coprime_card_oddCoreIn X))
        (Subgroup.card_dvd_of_le hXO)
    exact sig_not_isSolvable_of_isQuasisimple hXq (CFSG.FeitThompson.isSolvable_of_odd_natCard _ hXodd)
  · have hz := hle (show (⟨o, hoX⟩ : X) ∈ (oddCoreIn X).subgroupOf X from ho)
    have h1 := (mem_center_iff.mp hz) ⟨x, hx⟩
    exact (congrArg Subtype.val h1).symm

theorem isQuasisimple_and_forall_of_oddFullCoverAt (hB : TwoComponentsQuasisimpleAt T)
    {X Y : Subgroup T} (hXp : ⁅X, X⁆ = X) (hXq : IsQuasisimple (↥X ⧸ pPrimeCore 2 ↥X))
    (hYr : 2 ≤ CFSG.Open.pRank 2 Y) (hYX : Y ≤ normalizer (X : Set T))
    (hcomm : ⁅X, Y⁆ ≤ oddCoreIn X)
    (hcov : ∀ y ∈ Y, orderOf y = 2 → OddFullCoverAt X y) :
    CFSG.IsQuasisimple X ∧
      ∀ y ∈ Y, orderOf y = 2 → IsTwoComponentIn X (centralizer ({y} : Set T)) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hK : ∀ y : T, y ∈ Y → orderOf y = 2 → ∃ K : Subgroup T,
      IsTwoComponentIn K (centralizer ({y} : Set T)) ∧ CFSG.IsQuasisimple K ∧ K ≤ X ∧
        K ⊔ oddCoreIn X = X := fun y hy hy2 =>
    exists_component_le_of_oddFullCoverAt (hB y hy2) (hcov y hy hy2)
  choose! Kf hKf using hK
  have hYO : ∀ y ∈ Y, ∀ p ∈ oddCoreIn X, y * p * y⁻¹ ∈ oddCoreIn X := fun y hy p hp =>
    (mem_normalizer_iff.mp (mem_normalizer_iff_map_conj_eq.mpr (map_conj_oddCoreIn (hYX hy))) p).mp
      hp
  have hOodd : Odd (Nat.card (oddCoreIn X)) := Nat.coprime_two_left.mp (coprime_card_oddCoreIn X)
  have hXO : ∀ x ∈ X, ∀ p ∈ oddCoreIn X, ⁅x, p⁆ ∈ oddCoreIn X := fun x hx p hp => by
    have hxO : x ∈ normalizer (oddCoreIn X : Set T) :=
      mem_normalizer_iff_map_conj_eq.mpr (map_conj_oddCoreIn (le_normalizer hx))
    rw [commutatorElement_def]
    exact mul_mem ((mem_normalizer_iff.mp hxO p).mp hp) (inv_mem hp)
  have hcent : ∀ y : T, y ∈ Y → orderOf y = 2 → ∀ g : T, g ∈ centralizer ({y} : Set T) →
      g ∈ normalizer (X : Set T) → (∀ k ∈ Kf y, ⁅k, g⁆ ∈ oddCoreIn X) →
      g ∈ centralizer (Kf y : Set T) := fun y hy hy2 g hgy hgX hgc => by
    obtain ⟨h1, h2, h3, h4⟩ := hKf y hy hy2
    exact mem_centralizer_of_commutator_mem_oddCoreIn h2 h3
      (mem_normalizer_of_isTwoComponentIn_of_sup_eq hXq h1 h3 h4 (le_normalizer hgy) hgX) hgc
  have hconst : ∀ y₁ y₂ : T, y₁ ∈ Y → orderOf y₁ = 2 → y₂ ∈ Y → orderOf y₂ = 2 →
      y₁ * y₂ = y₂ * y₁ → Kf y₁ = Kf y₂ := by
    intro y₁ y₂ hy₁ hy₁2 hy₂ hy₂2 h12
    have hy₂C : y₂ ∈ centralizer ({y₁} : Set T) := mem_centralizer_singleton_iff.mpr h12.symm
    have hy₁C : y₁ ∈ centralizer ({y₂} : Set T) := mem_centralizer_singleton_iff.mpr h12
    have hc₁ := hcent y₁ hy₁ hy₁2 y₂ hy₂C (hYX hy₂) fun k hk =>
      hcomm (commutator_mem_commutator ((hKf y₁ hy₁ hy₁2).2.2.1 hk) hy₂)
    have hc₂ := hcent y₂ hy₂ hy₂2 y₁ hy₁C (hYX hy₁) fun k hk =>
      hcomm (commutator_mem_commutator ((hKf y₂ hy₂ hy₂2).2.2.1 hk) hy₁)
    have hle₁ : Kf y₁ ≤ centralizer ({y₂} : Set T) := fun k hk =>
      mem_centralizer_singleton_iff.mpr (mem_centralizer_iff.mp hc₁ k hk)
    have hle₂ : Kf y₂ ≤ centralizer ({y₁} : Set T) := fun k hk =>
      mem_centralizer_singleton_iff.mpr (mem_centralizer_iff.mp hc₂ k hk)
    have hH₁ : IsTwoComponentIn (Kf y₁) (centralizer ({y₁} : Set T) ⊓ centralizer ({y₂} : Set T)) :=
      isTwoComponentIn_of_le (hKf y₁ hy₁ hy₁2).1 (le_inf (hKf y₁ hy₁ hy₁2).1.1 hle₁) inf_le_left
    have hH₂ : IsTwoComponentIn (Kf y₂) (centralizer ({y₁} : Set T) ⊓ centralizer ({y₂} : Set T)) :=
      isTwoComponentIn_of_le (hKf y₂ hy₂ hy₂2).1 (le_inf hle₂ (hKf y₂ hy₂ hy₂2).1.1) inf_le_right
    exact eq_of_isTwoComponentIn_of_sup_eq hXq hH₁ hH₂ (hKf y₁ hy₁ hy₁2).2.2.1
      (hKf y₂ hy₂ hy₂2).2.2.1 (hKf y₁ hy₁ hy₁2).2.2.2 (hKf y₂ hy₂ hy₂2).2.2.2
  obtain ⟨E, hEY, hE, hEcard⟩ := SectionRank.exists_pRank one_lt_two Y
  have h4 : 2 < Nat.card E := by
    rw [hEcard]
    calc 2 < 2 ^ 2 := by norm_num
      _ ≤ 2 ^ CFSG.Open.pRank 2 Y := Nat.pow_le_pow_right (by norm_num) hYr
  have := Fintype.ofFinite ↥E
  rw [Nat.card_eq_fintype_card] at h4
  obtain ⟨a, b, c, hab, hac, hbc⟩ := Fintype.two_lt_card_iff.mp h4
  obtain ⟨u, v, hu1, hv1, huv⟩ : ∃ u v : E, u ≠ 1 ∧ v ≠ 1 ∧ u ≠ v := by
    by_cases ha : a = 1
    · exact ⟨b, c, fun h => hab (ha.trans h.symm), fun h => hac (ha.trans h.symm), hbc⟩
    · by_cases hb : b = 1
      · exact ⟨a, c, ha, fun h => hbc (hb.trans h.symm), hac⟩
      · exact ⟨a, b, ha, hb, hab⟩
  have hsq : ∀ z ∈ E, z * z = 1 := fun z hz => by rw [← sq]; exact hE.2 z hz
  set e₁ : T := (u : T) with he₁
  set e₂ : T := (v : T) with he₂
  have he₁E : e₁ ∈ E := u.2
  have he₂E : e₂ ∈ E := v.2
  have h12 : e₁ * e₂ = e₂ * e₁ := congrArg Subtype.val (hE.1.is_comm.comm u v)
  have he₁1 : e₁ ≠ 1 := fun h => hu1 (Subtype.ext h)
  have he₂1 : e₂ ≠ 1 := fun h => hv1 (Subtype.ext h)
  have he12 : e₁ ≠ e₂ := fun h => huv (Subtype.ext h)
  have hinv : ∀ z ∈ E, z ≠ 1 → orderOf z = 2 := fun z hz hz1 =>
    orderOf_eq_prime (by rw [sq]; exact hsq z hz) hz1
  have he₃E : e₁ * e₂ ∈ E := mul_mem he₁E he₂E
  have he₃1 : e₁ * e₂ ≠ 1 := fun h => he12 (by
    have := eq_inv_of_mul_eq_one_left h
    rwa [inv_eq_of_mul_eq_one_right (hsq e₂ he₂E)] at this)
  have he₁Y := hEY he₁E
  have he₂Y := hEY he₂E
  have he₃Y := hEY he₃E
  have ho₁ := hinv e₁ he₁E he₁1
  have ho₂ := hinv e₂ he₂E he₂1
  have ho₃ := hinv _ he₃E he₃1
  have hK12 : Kf e₁ = Kf e₂ := hconst e₁ e₂ he₁Y ho₁ he₂Y ho₂ h12
  have hK13 : Kf e₁ = Kf (e₁ * e₂) := hconst e₁ (e₁ * e₂) he₁Y ho₁ he₃Y ho₃ (by
    rw [← mul_assoc, hsq e₁ he₁E, one_mul, h12, mul_assoc, hsq e₁ he₁E, mul_one])
  set K := Kf e₁ with hKdef
  have hOK : ∀ e : T, e ∈ Y → orderOf e = 2 → Kf e = K →
      oddCoreIn X ⊓ centralizer ({e} : Set T) ≤ centralizer (K : Set T) := by
    intro e he he2 hKe o ho
    rw [← hKe]
    exact hcent e he he2 o ho.2 (le_normalizer (map_subtype_le _ ho.1)) fun k hk =>
      hXO k ((hKf e he he2).2.2.1 hk) o ho.1
  have hgen := CGT.T75H.le_sup_fixed_of_commuting_involutions hOodd (hsq e₁ he₁E)
    (hsq e₂ he₂E) h12 he₁1 he₂1 he12 (hYO e₁ he₁Y) (hYO e₂ he₂Y)
  have hOC : oddCoreIn X ≤ centralizer (K : Set T) :=
    hgen.trans (sup_le (sup_le (hOK e₁ he₁Y ho₁ rfl) (hOK e₂ he₂Y ho₂ hK12.symm))
      (hOK _ he₃Y ho₃ hK13.symm))
  have hKq := (hKf e₁ he₁Y ho₁).2.1
  have hXK : X ≤ K := sigPerfect_le_of_le_sup (hOC.trans (centralizer_le_normalizer _))
    (CFSG.FeitThompson.isSolvable_of_odd_natCard _ hOodd) hXp (hKf e₁ he₁Y ho₁).2.2.2.ge
  have hXeq : X = K := le_antisymm hXK (hKf e₁ he₁Y ho₁).2.2.1
  have hXqs : CFSG.IsQuasisimple X := hXeq ▸ hKq
  refine ⟨hXqs, fun y hy hy2 => ?_⟩
  obtain ⟨h1, -, h3, h4⟩ := hKf y hy hy2
  have hOy : oddCoreIn X ≤ normalizer (Kf y : Set T) := fun o ho => by
    refine centralizer_le_normalizer _ (mem_centralizer_iff.mpr fun k hk => ?_)
    exact (mul_comm_of_mem_oddCoreIn hXqs ho (h3 hk)).symm
  have hXy : X ≤ Kf y :=
    sigPerfect_le_of_le_sup hOy (CFSG.FeitThompson.isSolvable_of_odd_natCard _ hOodd) hXp h4.ge
  have heq : Kf y = X := le_antisymm h3 hXy
  exact heq ▸ h1

theorem singleComponentSimpleFullAt_of_clean {P : (S : Type) → [Group S] → Prop}
    (hB : ∀ (T : Type) [Group T] [Finite T], IsSimpleGroup T → (∃ a b : T, a * b ≠ b * a) →
      P T → TwoComponentsQuasisimpleAt T)
    (h : SingleComponentCleanAt P) : SingleComponentSimpleFullAt P := by
  intro T _ _ hT hP X Y hXp hYp hXq hYq hXr hYr hcomm hcovY hcovX
  have hna : ∃ a b : T, a * b ≠ b * a := by
    obtain ⟨-, -, ⟨u, v, huv⟩⟩ := hXq
    obtain ⟨u', rfl⟩ := QuotientGroup.mk_surjective u
    obtain ⟨v', rfl⟩ := QuotientGroup.mk_surjective v
    obtain ⟨u'', rfl⟩ := QuotientGroup.mk_surjective u'
    obtain ⟨v'', rfl⟩ := QuotientGroup.mk_surjective v'
    refine ⟨u'', v'', fun h => huv ?_⟩
    have h' : u'' * v'' = v'' * u'' := Subtype.ext h
    simp only [← QuotientGroup.mk_mul, h']
  have hBT := hB T hT hna hP
  have hcXY : ⁅X, Y⁆ ≤ oddCoreIn X := hcomm.trans inf_le_left
  have hcYX : ⁅Y, X⁆ ≤ oddCoreIn Y :=
    (Subgroup.commutator_comm Y X).le.trans (hcomm.trans inf_le_right)
  have hYX : Y ≤ normalizer (X : Set T) := fun y hy =>
    (le_coreActionKernel_of_commutator_le_oddCoreIn
      ((Subgroup.commutator_comm Y X).le.trans hcXY) hy).1
  have hXY : X ≤ normalizer (Y : Set T) := fun x hx =>
    (le_coreActionKernel_of_commutator_le_oddCoreIn
      ((Subgroup.commutator_comm X Y).le.trans hcYX) hx).1
  obtain ⟨hXqs, hXcomp⟩ :=
    isQuasisimple_and_forall_of_oddFullCoverAt hBT hXp hXq hYr hYX hcXY hcovX
  obtain ⟨hYqs, hYcomp⟩ :=
    isQuasisimple_and_forall_of_oddFullCoverAt hBT hYp hYq hXr hXY hcYX hcovY
  have hbot : ⁅X, Y⁆ = ⊥ := by
    rw [eq_bot_iff, commutator_le]
    intro x hx y hy
    have hyc : y ∈ centralizer (X : Set T) :=
      mem_centralizer_of_commutator_mem_oddCoreIn hXqs le_rfl (hYX hy)
        fun k hk => hcXY (commutator_mem_commutator hk hy)
    rw [mem_bot, commutatorElement_eq_one_iff_mul_comm]
    exact mem_centralizer_iff.mp hyc x hx
  exact h T hT hP X Y hXqs hYqs hXr hYr hbot hXcomp hYcomp

theorem singleComponentQuasisimpleAt_of_clean {P : (S : Type) → [Group S] → Prop}
    (hB : ∀ (T : Type) [Group T] [Finite T], IsSimpleGroup T → (∃ a b : T, a * b ≠ b * a) →
      P T → TwoComponentsQuasisimpleAt T)
    (h : SingleComponentCleanAt P) : SingleComponentQuasisimpleAt P :=
  singleComponentQuasisimpleAt_of_simpleFullAt (singleComponentSimpleFullAt_of_clean hB h)

end B

end CFSG.ComponentClassification.Sol76.Sig
