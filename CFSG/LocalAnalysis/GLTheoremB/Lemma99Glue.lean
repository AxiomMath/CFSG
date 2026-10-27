module

public import CFSG.LocalAnalysis.GLTheoremB.Lemma99Setup
public import CFSG.LocalAnalysis.GLTheoremB.CentralizerLift
public import CFSG.LocalAnalysis.RankThreeEvenClassification.CoprimeFactorization
public import CFSG.LocalAnalysis.GLTheoremB.Lemma99Core
public import CFSG.LocalAnalysis.GLTheoremB.PCompLift

public section

namespace CFSG.LocalAnalysis.GLTheoremB

open CFSG.Open

section Generic

variable {Q : Type*} [Group Q]

theorem commutator_le_centralizer_of_normalizes {S T K : Subgroup Q}
    (hS : S ≤ Subgroup.normalizer (K : Set Q)) (hT : K ≤ Subgroup.centralizer (T : Set Q)) :
    ⁅S, T⁆ ≤ Subgroup.centralizer (K : Set Q) := by
  refine Subgroup.commutator_le.2 fun s hs t ht => ?_
  rw [commutatorElement_def, Subgroup.mem_centralizer_iff]
  intro k hk
  have h1 : s⁻¹ * k * s ∈ K := by
    have := (Subgroup.mem_normalizer_iff.1 (hS (S.inv_mem hs)) k).1 hk
    simpa using this
  have h2 : t * (s⁻¹ * k * s) = (s⁻¹ * k * s) * t := (Subgroup.mem_centralizer_iff.1 (hT h1)) t ht
  have h3 : t⁻¹ * k = k * t⁻¹ := (Subgroup.mem_centralizer_iff.1 (hT hk)) t⁻¹ (T.inv_mem ht)
  calc k * (s * t * s⁻¹ * t⁻¹) = s * ((s⁻¹ * k * s) * t) * s⁻¹ * t⁻¹ := by group
    _ = s * (t * (s⁻¹ * k * s)) * s⁻¹ * t⁻¹ := by rw [h2]
    _ = s * t * s⁻¹ * (k * t⁻¹) := by group
    _ = s * t * s⁻¹ * (t⁻¹ * k) := by rw [h3]
    _ = (s * t * s⁻¹ * t⁻¹) * k := by group

theorem centralizer_zpowers_eq (d : Q) :
    Subgroup.centralizer ((Subgroup.zpowers d : Subgroup Q) : Set Q) =
      Subgroup.centralizer ({d} : Set Q) := by
  rw [Subgroup.zpowers_eq_closure, Subgroup.centralizer_closure]

end Generic

section Piece

variable {G : Type} [Group G] [Finite G] {m p : ℕ}

theorem not_barX_inf_le_centralizer (hp : p.Prime) (hp2 : p ≠ 2) {M Γ K : Subgroup G} {d : G}
    (hΓM : Γ ≤ M) (hdM : d ∈ M) (hΓ2 : IsPGroup 2 Γ) (hdΓ : d ∈ Subgroup.normalizer (Γ : Set G))
    (hd : IsPGroup p (Subgroup.zpowers d)) (hKd : K ≤ Subgroup.centralizer ({d} : Set G))
    (hΓK : barX p M Γ ≤ Subgroup.normalizer ((barX p M K : Subgroup (↥M ⧸ GLAPPrimeCore p ↥M)) :
      Set (↥M ⧸ GLAPPrimeCore p ↥M)))
    (hnc : ¬ barX p M Γ ≤ Subgroup.centralizer ((barX p M K :
      Subgroup (↥M ⧸ GLAPPrimeCore p ↥M)) : Set (↥M ⧸ GLAPPrimeCore p ↥M))) :
    ¬ barX p M (Γ ⊓ Subgroup.centralizer ({d} : Set G)) ≤
      Subgroup.centralizer ((barX p M K : Subgroup (↥M ⧸ GLAPPrimeCore p ↥M)) :
        Set (↥M ⧸ GLAPPrimeCore p ↥M)) := by
  intro hX
  apply hnc
  have hz : Subgroup.zpowers d ≤ M := (Subgroup.zpowers_le).2 hdM
  have hzΓ : Subgroup.zpowers d ≤ Subgroup.normalizer (Γ : Set G) := (Subgroup.zpowers_le).2 hdΓ
  have hfac := CFSG.RankThreeEvenClassification.Helpers.coprime_commutator_centralizer_factorization
    p hp (Subgroup.zpowers d) Γ hd (fun h => (Nat.Prime.coprime_iff_not_dvd hp).1
      (coprime_card_of_isPGroup_two hp hp2 hΓ2) h) hzΓ
  rw [centralizer_zpowers_eq] at hfac
  have hJΓ : ⁅Γ, Subgroup.zpowers d⁆ ≤ Γ :=
    Subgroup.le_normalizer_iff_commutator_le_left.1 hzΓ
  have hJM : ⁅Γ, Subgroup.zpowers d⁆ ≤ M := hJΓ.trans hΓM
  have hXM : Γ ⊓ Subgroup.centralizer ({d} : Set G) ≤ M := inf_le_left.trans hΓM
  have hsup : barX p M Γ ≤ barX p M ⁅Γ, Subgroup.zpowers d⁆ ⊔
      barX p M (Γ ⊓ Subgroup.centralizer ({d} : Set G)) := by
    have h1 := barX_mono (X := M) p hfac.le
    unfold barX at h1 ⊢
    rwa [Subgroup.subgroupOf_sup hJM hXM, Subgroup.map_sup] at h1
  refine hsup.trans (sup_le ?_ hX)
  rw [barX_commutator p hΓM hz]
  refine commutator_le_centralizer_of_normalizes hΓK ?_
  refine barX_le_centralizer fun s hs t ht _ _ => ?_
  have hc : s * t = t * s := by
    obtain ⟨n, rfl⟩ := ht
    have h : Commute d s := (Subgroup.mem_centralizer_singleton_iff.1 (hKd hs)).symm
    exact ((h.zpow_left n).eq).symm
  have : s * t * s⁻¹ * t⁻¹ = 1 := by rw [hc]; group
  rw [this]
  exact Subgroup.one_mem _

theorem commutator_eq_of_glaPComponent {p : ℕ} (hp : p.Prime) {M A K X : Subgroup G}
    (hAM : A ≤ M) (hK : GLAPComponent p A K) (hXM : X ≤ M)
    (hXK : X ≤ Subgroup.normalizer (K : Set G))
    (hKq : CFSG.Open.IsQuasisimple ↥(barX p M K))
    (hnc : ¬ barX p M X ≤ Subgroup.centralizer ((barX p M K : Subgroup (↥M ⧸ GLAPPrimeCore p ↥M)) :
      Set (↥M ⧸ GLAPPrimeCore p ↥M))) : ⁅X, K⁆ = K := by
  have hJK : ⁅X, K⁆ ≤ K := Subgroup.commutator_le.2 fun x hx k hk => by
    rw [commutatorElement_def]
    exact K.mul_mem ((Subgroup.mem_normalizer_iff.1 (hXK hx) k).1 hk) (K.inv_mem hk)
  have hJsn : IsSubnormal ⁅X, K⁆ A :=
    IsSubnormal.step hJK (normal_subgroupOf_commutator hXK) hK.2.1
  have hbarJ : barX p M ⁅X, K⁆ = barX p M K := by
    rw [barX_commutator p hXM (hK.1.trans hAM)]
    exact commutator_eq_of_isQuasisimple hKq (barX_le_normalizer hXK) hnc
  by_contra hne
  exact hK.2.2.2 _ (lt_of_le_of_ne hJK hne) hJsn
    (barX_eq_of_barX_eq hp hAM (hJK.trans hK.1) hK.1 hbarJ)

theorem isPiGroup_quot_of_barX {p : ℕ} (hp : p.Prime) {M K : Subgroup G} (hKM : K ≤ M)
    (h : IsPiGroup p ↥(barX p M K)) : IsPiGroup p (↥K ⧸ GLAPPrimeCore p ↥K) := by
  have : Fact p.Prime := ⟨hp⟩
  set ψ : ↥M →* ↥M ⧸ GLAPPrimeCore p ↥M := QuotientGroup.mk' (GLAPPrimeCore p ↥M) with hψ
  set A₀ : Subgroup ↥M := K.subgroupOf M with hA₀
  have hker : Nat.Coprime p (Nat.card ↥(A₀ ⊓ ψ.ker)) := by
    rw [hψ, QuotientGroup.ker_mk']
    exact Nat.Coprime.coprime_dvd_right (Subgroup.card_dvd_of_le inf_le_right)
      CFSG.pPrimeCore_coprime_card
  have e1 := lcEquiv hp ψ A₀ hker
  have hbot : GLAPPrimeCore p ↥(A₀.map ψ) = ⊥ := h.2.1
  have e2 : (↥(A₀.map ψ) ⧸ GLAPPrimeCore p ↥(A₀.map ψ)) ≃* ↥(A₀.map ψ) :=
    (QuotientGroup.quotientMulEquivOfEq hbot).trans QuotientGroup.quotientBot
  have e3 : ↥A₀ ≃* ↥K := Subgroup.subgroupOfEquivOfLe hKM
  have e4 : (↥A₀ ⧸ GLAPPrimeCore p ↥A₀) ≃* (↥K ⧸ GLAPPrimeCore p ↥K) :=
    QuotientGroup.congr _ _ e3 (glaPPrimeCore_map_iso p e3)
  exact IsPiGroup.of_mulEquiv ((e2.symm.trans e1.symm).trans e4) h

theorem lemma99_piece (hSch : CFSG.AGLEmbedding.KFactCatalogSchreier) (i20 : Input20_1)
    (i11 : Input11_6) (l23 : Lemma23) (hSt : GLStanding G m p) {B M : Subgroup G}
    (hB : IsBOneMax p B) (hM : IsPreUniquenessTwoLocal p B M) {D : Subgroup G} (hDB : D ≤ B)
    {d : G} (hd : d ∈ D) (hd1 : d ≠ 1) {L K : Subgroup G} (hL : GLAPComponent p M L)
    (hΓL : gammaD D ≤ Subgroup.normalizer (L : Set G)) (hΓM : gammaD D ≤ M)
    (hK : GLAPComponent p (L ⊓ Subgroup.centralizer ({d} : Set G)) K)
    (hKπ : IsPiGroup p ↥(barX p M K))
    (hΓK : barX p M (gammaD D) ≤ Subgroup.normalizer ((barX p M K :
      Subgroup (↥M ⧸ GLAPPrimeCore p ↥M)) : Set (↥M ⧸ GLAPPrimeCore p ↥M)))
    (hnc : ¬ barX p M (gammaD D) ≤ Subgroup.centralizer ((barX p M K :
      Subgroup (↥M ⧸ GLAPPrimeCore p ↥M)) : Set (↥M ⧸ GLAPPrimeCore p ↥M))) :
    K ≤ piOf p d ⊔ GLAPPrimeCoreOf p (Subgroup.centralizer ({d} : Set G)) := by
  have hp := hSt.prime
  have hp2 := hSt.ne_two
  have : Fact p.Prime := ⟨hp⟩
  set C := Subgroup.centralizer ({d} : Set G) with hC
  set A := L ⊓ C with hA
  set Γ := gammaD D with hΓ
  have hBM : B ≤ M := le_of_isPreUniquenessTwoLocal hSt hB hM
  have hdB : d ∈ B := hDB hd
  have hdM : d ∈ M := hBM hdB
  have hBC : B ≤ C := le_centralizer_of_mem hB.1.1 hdB
  have hAM : A ≤ M := inf_le_left.trans hL.1
  have hKA : K ≤ A := hK.1
  have hKM : K ≤ M := hKA.trans hAM
  have hKC : K ≤ C := hKA.trans inf_le_right
  have hΓ2 : IsPGroup 2 Γ := isPGroup_gammaD D
  have hBD : B ≤ Subgroup.normalizer (D : Set G) := fun b hb =>
    Subgroup.centralizer_le_normalizer (D : Set G) (Subgroup.mem_centralizer_iff.2 fun y hy =>
      elemAbelian_comm hB.1.1 (hDB hy) hb)
  have hBΓ : B ≤ Subgroup.normalizer (Γ : Set G) := fun b hb =>
    normalizer_le_normalizer_gammaD D (hBD hb)
  have hdz : IsPGroup p (Subgroup.zpowers d) :=
    (isPGroup_of_isElemAbelian' hB.1.1).to_le ((Subgroup.zpowers_le).2 hdB)
  set X := Γ ⊓ C with hX
  have hXM : X ≤ M := inf_le_left.trans hΓM
  have hXN : X ≤ Subgroup.normalizer (K : Set G) := by
    intro x hx
    have hxA : x ∈ Subgroup.normalizer (A : Set G) :=
      mem_normalizer_inf (hΓL hx.1) (Subgroup.le_normalizer hx.2)
    exact mem_normalizer_of_barX_normalizes hp hAM hK (hXM hx) hxA
      (hΓK ⟨⟨x, hXM hx⟩, (Subgroup.mem_subgroupOf).2 hx.1, rfl⟩)
  have hnc' := not_barX_inf_le_centralizer hp hp2 hΓM hdM hΓ2 (hBΓ hdB) hdz
    (fun k hk => hK.1 hk |>.2) hΓK hnc
  have hcov : ⁅X, K⁆ = K :=
    commutator_eq_of_glaPComponent hp hAM hK hXM hXN hKπ.1 hnc'
  have hKπ' : IsPiGroup p (↥K ⧸ GLAPPrimeCore p ↥K) := isPiGroup_quot_of_barX hp hKM hKπ
  have hKsn : IsSubnormal K (M ⊓ C) :=
    isSubnormal_trans' hK.2.1 (isSubnormal_inf hL.2.1 C)
  have hBX : B ≤ Subgroup.normalizer (X : Set G) := fun b hb =>
    mem_normalizer_inf (hBΓ hb) (Subgroup.le_normalizer (hBC hb))
  exact lemma99_core hSch i20 i11 l23 hSt hB hM hdB hd1 hKM hKC hKsn (glaPComponent_perfect hK)
    hKπ' inf_le_right (hΓ2.to_le inf_le_left) hBX hcov

end Piece

end CFSG.LocalAnalysis.GLTheoremB
