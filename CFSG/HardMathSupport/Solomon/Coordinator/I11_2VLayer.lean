module

public import CFSG.HardMathSupport.Timmesfeld.ComponentBalance.I_11_2_Layer
public import CFSG.LocalAnalysis.GLTheoremB.PCompLift
import CFSG.HardMathSupport.Timmesfeld.ComponentBalance.I_11_6_PartIIExists
import CFSG.Quasithin.Background.F918V5GComp

public section

namespace CFSG.HardMathSupport.Solomon.Coordinator

open CFSG.Open CFSG.LocalAnalysis.GLTheoremB CFSG.HardMathSupport.Timmesfeld.ComponentBalance

theorem i112v_layer {X : Type*} [Group X] [Finite X] {p : ℕ} (hp : p.Prime)
    (hO : GLAPPrimeCore p X = ⊥) {B : Subgroup X} (hB : IsElemAbelian p B)
    {L : Subgroup X} (hL : GLAPComponent p ⊤ L)
    (hidx : (Subgroup.normalizer (L : Set X)).relIndex B = p)
    {b : X} (hb : b ∈ B) (hbn : b ∉ Subgroup.normalizer (L : Set X))
    (hZL : Nat.card ↥(L ⊓ Subgroup.centralizer (L : Set X)) = 1 ∨
      Nat.card ↥(L ⊓ Subgroup.centralizer (L : Set X)) = p)
    (hZ : Nat.card ↥((⨆ g ∈ B, GLBConj g L) ⊓
      Subgroup.centralizer ((⨆ g ∈ B, GLBConj g L : Subgroup X) : Set X)) < p ^ p) :
    IsSimpleGroup ↥(GLAPLayer p (Subgroup.centralizer ({b} : Set X) ⊓ ⨆ g ∈ B, GLBConj g L)) ∧
      p ∣ Nat.card ↥(GLAPLayer p (Subgroup.centralizer ({b} : Set X) ⊓ ⨆ g ∈ B, GLBConj g L)) ∧
      Nonempty (↥(GLAPLayer p (Subgroup.centralizer ({b} : Set X) ⊓ ⨆ g ∈ B, GLBConj g L)) ≃*
        (↥L ⧸ Subgroup.center ↥L)) := by
  have : Fact p.Prime := ⟨hp⟩
  have : NeZero p := ⟨hp.ne_zero⟩
  have hbp : b ^ p = 1 := hB.2 b hb
  have hLc : IsComponentOf L ⊤ := i116pI_isComponentOf hO hL
  have hq : CFSG.Open.IsQuasisimple ↥L := i116e_isQuasisimple hO hL
  have hcomm : LComm p b L := by
    intro i j hij x y
    have hmem : ∀ k : ZMod p, ∀ x : ↥L, lphi p b L k x ∈ GLBConj (lbp p b k) L := by
      intro k x
      rw [mem_gLBConj, lphi_apply]
      have : lbp p b k * ((lbp p b k)⁻¹ * (x : X) * lbp p b k) * (lbp p b k)⁻¹ = x := by group
      rw [this]
      exact x.2
    rcases CFSG.Quasithin.F918V5G.isComponentOf_eq_or_commute
      (isComponentOf_gLBConj hLc (lbp p b i)) (isComponentOf_gLBConj hLc (lbp p b j)) with h | h
    · exact absurd h (gLBConj_lbp_ne hp hbp hbn hij)
    · exact h _ (hmem i x) _ (hmem j y)
  have hJ := J_eq_range hp hb hbp hbn hidx hcomm
  rw [hJ] at hZ ⊢
  have hZc : Nat.card (Subgroup.center ↥L) = 1 ∨ Nat.card (Subgroup.center ↥L) = p := by
    rwa [← card_center_eq]
  have hZ0 : ∀ x ∈ Subgroup.center ↥L, lN hcomm x = 1 := by
    rcases lN_center_trivial_or hbp hcomm hZc with h | h
    · exact h
    · exfalso
      have hle : (Subgroup.pi Set.univ (fun _ : ZMod p => Subgroup.center ↥L)).map (lPsi hcomm) ≤
          (lPsi hcomm).range ⊓
            Subgroup.centralizer (((lPsi hcomm).range : Subgroup X) : Set X) := by
        rintro _ ⟨f, hf, rfl⟩
        refine ⟨⟨f, rfl⟩, Subgroup.mem_centralizer_iff.2 ?_⟩
        rintro _ ⟨g, rfl⟩
        exact (lPsi_central hcomm (fun k => hf k (Set.mem_univ k)) g).symm.eq
      have := Subgroup.card_le_of_le hle
      omega
  have hker : (lN hcomm).ker = Subgroup.center ↥L :=
    le_antisymm (fun x hx => lN_ker_le hcomm hx) (fun x hx => MonoidHom.mem_ker.2 (hZ0 x hx))
  have hsq : IsSimpleGroup (↥L ⧸ Subgroup.center ↥L) := hq.2
  let e : ↥(lN hcomm).range ≃* (↥L ⧸ Subgroup.center ↥L) :=
    (QuotientGroup.quotientKerEquivRange (lN hcomm)).symm.trans
      (QuotientGroup.quotientMulEquivOfEq hker)
  have hs : IsSimpleGroup ↥(lN hcomm).range := MulEquiv.isSimpleGroup e
  have hperf : ⁅(lN hcomm).range, (lN hcomm).range⁆ = (lN hcomm).range := by
    have h1 : ⁅(⊤ : Subgroup ↥L), (⊤ : Subgroup ↥L)⁆ = ⊤ := by
      have := hq.1
      rwa [commutator_def] at this
    rw [MonoidHom.range_eq_map, ← Subgroup.map_commutator, h1]
  have hdvd : p ∣ Nat.card ↥(lN hcomm).range := by
    rw [Nat.card_congr e.toEquiv, ← Subgroup.index_eq_card]
    exact dvd_index_center hp hq (i116e_dvd_card hp hO hL) hZc
  have hNC : (lN hcomm).range ≤
      Subgroup.centralizer ({b} : Set X) ⊓ (lPsi hcomm).range := by
    rintro _ ⟨l, rfl⟩
    refine ⟨Subgroup.mem_centralizer_singleton_iff.2 ?_, ⟨fun _ => l, rfl⟩⟩
    have := lN_conj hbp hcomm l
    calc lN hcomm l * b = b * (b⁻¹ * lN hcomm l * b) := by group
      _ = b * lN hcomm l := by rw [this]
  have hCN : ∀ c ∈ Subgroup.centralizer ({b} : Set X) ⊓ (lPsi hcomm).range,
      ∃ n ∈ (lN hcomm).range, ∃ y : X,
        (∀ d ∈ Subgroup.centralizer ({b} : Set X) ⊓ (lPsi hcomm).range, y * d = d * y) ∧
          c = n * y := by
    rintro c ⟨hcen, f, rfl⟩
    have h1 := Subgroup.mem_centralizer_singleton_iff.1 hcen
    have h2 : b⁻¹ * lPsi hcomm f * b = lPsi hcomm f := by
      calc b⁻¹ * lPsi hcomm f * b = b⁻¹ * (b * lPsi hcomm f) := by rw [mul_assoc, ← h1]
        _ = lPsi hcomm f := by group
    obtain ⟨l, z, hz, hfz⟩ := lPsi_centralizer hbp hcomm h2
    refine ⟨lN hcomm l, ⟨l, rfl⟩, lPsi hcomm z, ?_, hfz⟩
    rintro d ⟨_, g, rfl⟩
    exact (lPsi_central hcomm hz g).eq
  have hlay := glaPLayer_eq_of_central_product hp hs hperf hNC hdvd hCN
  rw [hlay]
  exact ⟨hs, hdvd, ⟨e⟩⟩

theorem i112v_glaPPrimeCore_eq_bot {p : ℕ} (hp : p.Prime) {K : Type*} [Group K] [Finite K]
    [IsSimpleGroup K] (hdvd : p ∣ Nat.card K) : GLAPPrimeCore p K = ⊥ := by
  have : Fact p.Prime := ⟨hp⟩
  rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal (GLAPPrimeCore p K) with h | h
  · exact h
  · exfalso
    have hc : Nat.Coprime p (Nat.card (GLAPPrimeCore p K)) := CFSG.pPrimeCore_coprime_card
    rw [h, Subgroup.card_top] at hc
    exact (Nat.Prime.coprime_iff_not_dvd hp).1 hc hdvd

section Lift

variable {G : Type*} [Group G] [Finite G] {p : ℕ}

omit [Finite G] in
theorem i112v_glaPComponent_of_layer_simple (hp : p.Prime) {C : Subgroup G}
    (hs : IsSimpleGroup ↥(GLAPLayer p C)) :
    GLAPComponent p C (GLAPLayer p C) ∧ ∀ K, GLAPComponent p C K → K = GLAPLayer p C := by
  have : Fact p.Prime := ⟨hp⟩
  have : IsSimpleGroup ↥(GLAPLayer p C) := hs
  have hle : ∀ K, GLAPComponent p C K → K ≤ GLAPLayer p C := fun K hK => le_sSup hK
  have hLC : GLAPLayer p C ≤ C := sSup_le fun K hK => hK.1
  have hne : ∀ K, GLAPComponent p C K → K ≠ ⊥ := by
    intro K hK hKb
    have hnt : Nontrivial (barX p C K) :=
      CFSG.ComponentClassification.Quasisimple.nontrivial hK.2.2.1.2.2
    apply (Subgroup.nontrivial_iff_ne_bot _).1 hnt
    rw [hKb]
    unfold barX
    rw [Subgroup.bot_subgroupOf, Subgroup.map_bot]
  have huniq : ∀ K, GLAPComponent p C K → K = GLAPLayer p C := fun K hK =>
    eq_of_isSubnormal_of_simple (isSubnormal_of_le_of_le hK.2.1 (hle K hK) hLC) (hne K hK)
  refine ⟨?_, huniq⟩
  by_contra hno
  have hset : {K | GLAPComponent p C K} = ∅ := by
    ext K
    simp only [Set.mem_ofPred_eq, Set.mem_empty_iff_false, iff_false]
    intro hK
    exact hno (huniq K hK ▸ hK)
  have hbot : GLAPLayer p C = ⊥ := by
    unfold GLAPLayer
    rw [hset, sSup_empty]
  exact (Subgroup.nontrivial_iff_ne_bot _).1 IsSimpleGroup.toNontrivial hbot

theorem i112v_layer_lift (hp : p.Prime) {X H : Subgroup G} (hHX : H ≤ X)
    (hs : IsSimpleGroup ↥(GLAPLayer p (barX p X H))) :
    GLAPComponent p H (GLAPLayer p H) ∧
      Nonempty ((↥(GLAPLayer p H) ⧸ GLAPPrimeCore p ↥(GLAPLayer p H)) ≃*
        (↥(GLAPLayer p (barX p X H)) ⧸ GLAPPrimeCore p ↥(GLAPLayer p (barX p X H)))) := by
  classical
  have : Fact p.Prime := ⟨hp⟩
  set A : Subgroup ↥X := H.subgroupOf X with hA
  set ψ : ↥X →* ↥X ⧸ GLAPPrimeCore p ↥X := QuotientGroup.mk' (GLAPPrimeCore p ↥X) with hψ
  have hAmap : A.map X.subtype = H := by
    rw [hA, Subgroup.subgroupOf_map_subtype, inf_eq_left.2 hHX]
  have hk1 : ∀ S : Subgroup ↥X, Nat.Coprime p (Nat.card ↥(S ⊓ X.subtype.ker)) := by
    intro S
    rw [(MonoidHom.ker_eq_bot_iff _).2 X.subtype_injective, inf_bot_eq, Subgroup.card_bot]
    exact Nat.coprime_one_right p
  have hk2 : ∀ S : Subgroup ↥X, Nat.Coprime p (Nat.card ↥(S ⊓ ψ.ker)) := by
    intro S
    rw [hψ, QuotientGroup.ker_mk']
    exact Nat.Coprime.coprime_dvd_right (Subgroup.card_dvd_of_le inf_le_right)
      CFSG.pPrimeCore_coprime_card
  obtain ⟨hDc, hDu⟩ := i112v_glaPComponent_of_layer_simple hp hs
  obtain ⟨K', hK', hK'D⟩ := exists_glaPComponent_map_eq hp ψ (hk2 A)
    (hDc : GLAPComponent p (A.map ψ) (GLAPLayer p (barX p X H)))
  have hall : ∀ K₁, GLAPComponent p A K₁ → K₁.map ψ = GLAPLayer p (barX p X H) :=
    fun K₁ h => hDu _ (glaPComponent_map hp ψ (hk2 A) h)
  have huA : ∀ K₁, GLAPComponent p A K₁ → K₁ = K' := by
    intro K₁ h
    refine glaPComponent_unique h hK' ?_
    have key : (barX p A K₁).map (lcMonoidHom hp ψ A (hk2 A)) =
        (barX p A K').map (lcMonoidHom hp ψ A (hk2 A)) := by
      rw [lcEquiv_barX hp ψ A (hk2 A) h.1, lcEquiv_barX hp ψ A (hk2 A) hK'.1, hall K₁ h, hK'D]
    exact Subgroup.map_injective (lcEquiv hp ψ A (hk2 A)).injective key
  have hK₀c : GLAPComponent p H (K'.map X.subtype) := by
    have := glaPComponent_map hp X.subtype (hk1 A) hK'
    rwa [hAmap] at this
  have huH : ∀ K, GLAPComponent p H K → K = K'.map X.subtype := by
    intro K hK
    rw [← hAmap] at hK
    obtain ⟨K₁, hK₁, rfl⟩ := exists_glaPComponent_map_eq hp X.subtype (hk1 A) hK
    rw [huA K₁ hK₁]
  have hlayH : GLAPLayer p H = K'.map X.subtype := by
    have hset : {K | GLAPComponent p H K} = {K'.map X.subtype} := by
      ext K
      exact ⟨fun h => huH K h, fun h => by rw [Set.mem_singleton_iff.1 h]; exact hK₀c⟩
    unfold GLAPLayer
    rw [hset, sSup_singleton]
  refine ⟨by rw [hlayH]; exact hK₀c, ?_⟩
  rw [hlayH, ← hK'D]
  exact ⟨(lcEquiv hp X.subtype K' (hk1 K')).symm.trans (lcEquiv hp ψ K' (hk2 K'))⟩

end Lift

end CFSG.HardMathSupport.Solomon.Coordinator
