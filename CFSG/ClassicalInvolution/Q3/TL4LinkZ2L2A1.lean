module

public import CFSG.ClassicalInvolution.Q3.TL4S289Brg
public import CFSG.ClassicalInvolution.Q3.TL4OddMu4W
public import CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinSetCore
public import CFSG.ClassicalInvolution.Q3.TL4OddZTR
public import CFSG.ClassicalInvolution.Q3.TL4VtxMainB

public section

namespace CFSG.ClassicalInvolution.Q3.TL4

open CFSG CFSG.Open CFSG.ClassicalInvolution CFSG.ClassicalInvolution.Generic
open CFSG.ClassicalInvolution.Asc77 CFSG.ClassicalInvolution.Balance
open CFSG.ClassicalInvolution.Disconnected.AschTight
open CFSG.ClassicalInvolution.Asc77.T8 (XMem)

namespace LinkZ2A

section Vertex

variable {G : Type} [Group G]

theorem hyp51At_of_forall_not {B : Subgroup G} {c : G}
    (h : ∀ L : Subgroup (OddQuot c), CFSG.IsComponent L → ¬ MovedByAll B c L) : Hyp51At B c :=
  ⟨fun L₁ _ h₁ _ hm _ => absurd hm (h L₁ h₁), fun L hL hm => absurd hm (h L hL)⟩

variable [Finite G]

theorem not_movedByAll_of_layer {Λ B : Subgroup G} {a x b : G}
    (hΛ : Λ ≤ Subgroup.centralizer ({a} : Set G))
    (hN : ∀ c ∈ Subgroup.centralizer ({a} : Set G), ∀ y ∈ Λ, c * y * c⁻¹ ∈ Λ)
    (hB : IsElemAbelian 2 B) (haB : a ∈ B) (ha1 : a ≠ 1) (hxB : x ∈ B) (hx1 : x ≠ 1)
    (hxa : x ≠ a) (hxΛ : x ∈ Λ) (hbB : b ∈ B) (hb1 : b ≠ 1) (hba : b ≠ a)
    (htriv : ∀ y ∈ Λ, b * y * b⁻¹ * y⁻¹ ∈ oddCoreOf Λ) :
    ∀ L : Subgroup (OddQuot a), CFSG.IsComponent L → ¬ MovedByAll B a L := by
  intro L hL hm
  have hcomm : b * a = a * b :=
    congrArg Subtype.val (hB.1.is_comm.comm ⟨b, hbB⟩ ⟨a, haB⟩)
  have hxC : x ∈ Subgroup.centralizer ({a} : Set G) := hΛ hxΛ
  have hbC : b ∈ Subgroup.centralizer ({a} : Set G) :=
    Subgroup.mem_centralizer_singleton_iff.mpr hcomm
  have hmx := hm _ (oddQuotMk_mem_modOdd hxB hxC)
    (Lemma52Proof.oddQuotMk_not_mem_zpowers hB haB ha1 hxB hx1 hxa hxC)
  have hLN : L ≤ modOdd a Λ :=
    S289.le_of_moved (S289.modOdd_normal hN) hL (oddQuotMk_mem_modOdd hxΛ hxC) hmx
  exact S289.not_movedByAll_of_trivialOn hΛ hN hbB hbC
    (Lemma52Proof.oddQuotMk_not_mem_zpowers hB haB ha1 hbB hb1 hba hbC) htriv hLN hm

end Vertex

section Frame


variable {n : ℕ} {Y : Type} [Group Y] [Finite Y] {R : Subgroup Y} {S : Sylow 2 R} {t : Y}

theorem hyp51At_wcoset (h4 : Thm4RBelow 3 n) (h5 : Thm5RBelowF 3 n)
    (htw : PhilipHall.Frame.Thm1RTwinLiftSetEBelow n) (hE4 : E4AutOddFreeR)
    (hL : TightLargeHypR 3 n Y R S t) {J : Subgroup Y}
    (hJ : J ∈ omegaNbr (CoreAssembly.conjClass (tightCore R)) (tightCore R)) {u : Y}
    (hu : IsUniqueInvolution J u) {w : Y} (hwt : w * t = t * w) (hwu : w * u = u * w)
    (hBe : IsElemAbelian 2 (Subgroup.closure ({t, u, w} : Set Y)))
    (hBelow : CIT3Below (Nat.card Y))
    (hcent : ∀ x : Y, x * t = t * x → x * u = u * x → x * w = w * x →
      ∀ c ∈ Subgroup.closure ({t, u, w} : Set Y), x * c = c * x)
    (hEB : Subgroup.closure ({t, u} : Set Y) ≤ Subgroup.closure ({t, u, w} : Set Y)) {e' : Y}
    (he' : e' ∈ Subgroup.closure ({t, u} : Set Y))
    (hwB : w ∈ Subgroup.closure ({t, u, w} : Set Y)) (hc1 : e' * w ≠ 1)
    (hwE : w ∉ Subgroup.closure ({t, u} : Set Y)) {R₀ : Subgroup Y}
    (hR₀ : IsSylow2In R₀ (tightCore R)) (hR₀u : R₀ ≤ Subgroup.centralizer ({u} : Set Y))
    (hR₀w : R₀ ≤ Subgroup.centralizer ({w} : Set Y)) {T₀ : Subgroup Y} (hT₀ : IsSylow2In T₀ J)
    (hT₀N : T₀ ≤ Subgroup.normalizer ((tightCore R : Subgroup Y) : Set Y))
    (hT₀w : T₀ ≤ Subgroup.centralizer ({w} : Set Y)) :
    Hyp51At (Subgroup.closure ({t, u, w} : Set Y)) (e' * w) := by
  have h := TightLargeHypR.typeRFam hL
  have hΩ := h.hyp
  have ht := hL.datum.isUniqueInvolution_core
  have hK : tightCore R ∈ CoreAssembly.conjClass (tightCore R) :=
    CoreAssembly.mem_conjClass_self _
  have ctu : t * u = u * t := Q3CL.T8.mul_comm_of_mem_omegaNbr hΩ ht hJ hu
  have htu : t ≠ u := fun h' => hJ.2.1 (eq_core_of_isUniqueInvolution hL hJ.1 (h' ▸ hu))
  have htE : t ∈ Subgroup.closure ({t, u} : Set Y) := Subgroup.subset_closure (by simp)
  have huE : u ∈ Subgroup.closure ({t, u} : Set Y) := Subgroup.subset_closure (by simp)
  have hne : ∀ x ∈ Subgroup.closure ({t, u} : Set Y), x ≠ e' * w := by
    intro x hx hxc
    apply hwE
    have h1 : e'⁻¹ * x ∈ Subgroup.closure ({t, u} : Set Y) :=
      Subgroup.mul_mem _ (Subgroup.inv_mem _ he') hx
    rwa [hxc, inv_mul_cancel_left] at h1
  have hcB' : e' * w ∈ Subgroup.closure ({t, u, w} : Set Y) := Subgroup.mul_mem _ (hEB he') hwB
  have hgen : Subgroup.closure ({t, u, w} : Set Y) =
      Subgroup.closure ({t, u, e' * w} : Set Y) := by
    have htC : t ∈ Subgroup.closure ({t, u, e' * w} : Set Y) := Subgroup.subset_closure (by simp)
    have huC : u ∈ Subgroup.closure ({t, u, e' * w} : Set Y) := Subgroup.subset_closure (by simp)
    have hcC : e' * w ∈ Subgroup.closure ({t, u, e' * w} : Set Y) :=
      Subgroup.subset_closure (by simp)
    have hE' : Subgroup.closure ({t, u} : Set Y) ≤ Subgroup.closure ({t, u, e' * w} : Set Y) := by
      rw [Subgroup.closure_le]
      intro v hv
      simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hv
      rcases hv with hv | hv <;> rw [hv]
      · exact htC
      · exact huC
    apply le_antisymm
    · rw [Subgroup.closure_le]
      intro v hv
      simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hv
      rcases hv with hv | hv | hv <;> rw [hv]
      · exact htC
      · exact huC
      · have h1 : e'⁻¹ * (e' * w) ∈ Subgroup.closure ({t, u, e' * w} : Set Y) :=
          Subgroup.mul_mem _ (Subgroup.inv_mem _ (hE' he')) hcC
        rwa [inv_mul_cancel_left] at h1
    · rw [Subgroup.closure_le]
      intro v hv
      simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hv
      rcases hv with hv | hv | hv <;> rw [hv]
      · exact hEB htE
      · exact hEB huE
      · exact hcB'
  have hct : e' * w * t = t * (e' * w) := (hcent t rfl ctu hwt.symm _ hcB').symm
  have hcu : e' * w * u = u * (e' * w) := (hcent u ctu.symm rfl hwu.symm _ hcB').symm
  have hMa : XMem (CoreAssembly.conjClass (tightCore R)) (e' * w) (tightCore R) := by
    refine ⟨hK, h.tight _ hK t ht (Subgroup.mem_centralizer_singleton_iff.mpr hct), R₀, hR₀,
      fun x hx => hcent x ?_ (Subgroup.mem_centralizer_singleton_iff.mp (hR₀u hx))
        (Subgroup.mem_centralizer_singleton_iff.mp (hR₀w hx)) _ hcB'⟩
    exact Subgroup.mem_centralizer_singleton_iff.mp
      (S1916.normalizer_le_centralizer_of_isUniqueInvolution ht
        (Subgroup.le_normalizer (hR₀.1 hx)))
  have hTc : ∀ x ∈ T₀, x * (e' * w) = e' * w * x := fun x hx => hcent x
    (Subgroup.mem_centralizer_singleton_iff.mp
      (S1916.normalizer_le_centralizer_of_isUniqueInvolution ht (hT₀N hx)))
    (Subgroup.mem_centralizer_singleton_iff.mp
      (S1916.normalizer_le_centralizer_of_isUniqueInvolution hu
        (Subgroup.le_normalizer (hT₀.1 hx))))
    (Subgroup.mem_centralizer_singleton_iff.mp (hT₀w hx)) _ hcB'
  have hMb : XMem (CoreAssembly.conjClass (tightCore R)) (e' * w) J :=
    ⟨hJ.1, h.tight _ hJ.1 u hu (Subgroup.mem_centralizer_singleton_iff.mpr hcu), T₀, hT₀, hTc⟩
  have htwS := PhilipHall.Frame.Thm1RTwinLiftSetEBelow.toSet htw
  exact hyp51At_of_vtxPair h4 h5 htwS hE4 hBelow hL.center hL.card.le h hBe hgen hc1
    ht.ne_one (hne t htE) hu.ne_one (hne u huE) htu (hne (t * u) (Subgroup.mul_mem _ htE huE))
    hMa hMb ht hu hT₀ (fun x hx => Subgroup.mem_centralizer_singleton_iff.mpr (hTc x hx)) hT₀N

theorem hyp51_z2Frame (h4 : Thm4RBelow 3 n) (h5 : Thm5RBelowF 3 n)
    (htw : PhilipHall.Frame.Thm1RTwinLiftSetEBelow n) (hE4 : E4AutOddFreeR)
    (hOm : OmegaAutOddFreeR) (hL : TightLargeHypR 3 n Y R S t) {J : Subgroup Y}
    (hJ : J ∈ omegaNbr (CoreAssembly.conjClass (tightCore R)) (tightCore R)) {u : Y}
    (hu : IsUniqueInvolution J u) {w : Y} (hw2 : w * w = 1) (hwt : w * t = t * w)
    (hwu : w * u = u * w) (hwE : w ∉ Subgroup.closure ({t, u} : Set Y)) {R₀ : Subgroup Y}
    (hR₀ : IsSylow2In R₀ (tightCore R)) (hR₀u : R₀ ≤ Subgroup.centralizer ({u} : Set Y))
    (hR₀w : R₀ ≤ Subgroup.centralizer ({w} : Set Y)) {T₀ : Subgroup Y} (hT₀ : IsSylow2In T₀ J)
    (hT₀N : T₀ ≤ Subgroup.normalizer ((tightCore R : Subgroup Y) : Set Y))
    (hT₀w : T₀ ≤ Subgroup.centralizer ({w} : Set Y))
    (htrivt : ∀ y ∈ linkLayer R t, w * y * w⁻¹ * y⁻¹ ∈ oddCoreOf (linkLayer R t))
    (htrivu : ∀ y ∈ linkLayerAt (CoreAssembly.conjClass (tightCore R)) J u,
      w * y * w⁻¹ * y⁻¹ ∈ oddCoreOf (linkLayerAt (CoreAssembly.conjClass (tightCore R)) J u)) :
    Hyp51 (Subgroup.closure ({t, u, w} : Set Y)) := by
  have h := TightLargeHypR.typeRFam hL
  have hΩ := h.hyp
  have ht := hL.datum.isUniqueInvolution_core
  have hK : tightCore R ∈ CoreAssembly.conjClass (tightCore R) :=
    CoreAssembly.mem_conjClass_self _
  have ctu : t * u = u * t := Q3CL.T8.mul_comm_of_mem_omegaNbr hΩ ht hJ hu
  have htu : t ≠ u := fun h' => hJ.2.1 (eq_core_of_isUniqueInvolution hL hJ.1 (h' ▸ hu))
  have hw1 : w ≠ 1 := fun h' => hwE (h' ▸ Subgroup.one_mem _)
  have hBe : IsElemAbelian 2 (Subgroup.closure ({t, u, w} : Set Y)) :=
    T8T.isElemAbelian_closure_three ht.sq hu.sq hw2 ctu hwt.symm hwu.symm
  have hB8 : Nat.card ↥(Subgroup.closure ({t, u, w} : Set Y)) = 8 :=
    T8T.natCard_closure_three ht.sq hu.sq hw2 ctu hwt.symm hwu.symm ht.ne_one hu.ne_one htu hw1
      hwE
  have hBelow : CIT3Below (Nat.card Y) := by
    rw [hL.card]
    exact hL.below
  have htB : t ∈ Subgroup.closure ({t, u, w} : Set Y) := Subgroup.subset_closure (by simp)
  have huB : u ∈ Subgroup.closure ({t, u, w} : Set Y) := Subgroup.subset_closure (by simp)
  have hwB : w ∈ Subgroup.closure ({t, u, w} : Set Y) := Subgroup.subset_closure (by simp)
  have htE : t ∈ Subgroup.closure ({t, u} : Set Y) := Subgroup.subset_closure (by simp)
  have huE : u ∈ Subgroup.closure ({t, u} : Set Y) := Subgroup.subset_closure (by simp)
  have hEB : Subgroup.closure ({t, u} : Set Y) ≤ Subgroup.closure ({t, u, w} : Set Y) := by
    rw [Subgroup.closure_le]
    intro v hv
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hv
    rcases hv with hv | hv <;> rw [hv]
    · exact htB
    · exact huB
  have hcent : ∀ x : Y, x * t = t * x → x * u = u * x → x * w = w * x →
      ∀ c ∈ Subgroup.closure ({t, u, w} : Set Y), x * c = c * x := by
    intro x hxt hxu hxw c hc
    have hle : Subgroup.closure ({t, u, w} : Set Y) ≤ Subgroup.centralizer ({x} : Set Y) := by
      rw [Subgroup.closure_le]
      intro v hv
      simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hv
      rcases hv with hv | hv | hv <;> rw [hv]
      · exact Subgroup.mem_centralizer_singleton_iff.mpr hxt.symm
      · exact Subgroup.mem_centralizer_singleton_iff.mpr hxu.symm
      · exact Subgroup.mem_centralizer_singleton_iff.mpr hxw.symm
    exact (Subgroup.mem_centralizer_singleton_iff.mp (hle hc)).symm
  have hK₀J : tightCore R ∈ omegaNbr (CoreAssembly.conjClass (tightCore R)) J :=
    Q3CL.T3.omegaNbr_symm Sec6Gen.l6_2Gen hΩ hK hJ.1 hJ
  have huΛ : u ∈ linkLayer R t :=
    coreAt_le_linkLayerAt hJ (mem_coreAt_of_sq_sq hu.mem (by rw [hu.sq, one_mul]) ctu.symm)
  have htΛ : t ∈ linkLayerAt (CoreAssembly.conjClass (tightCore R)) J u :=
    coreAt_le_linkLayerAt hK₀J (mem_coreAt_of_sq_sq ht.mem (by rw [ht.sq, one_mul]) ctu)
  have hNu : ∀ c ∈ Subgroup.centralizer ({u} : Set Y),
      ∀ y ∈ linkLayerAt (CoreAssembly.conjClass (tightCore R)) J u,
        c * y * c⁻¹ ∈ linkLayerAt (CoreAssembly.conjClass (tightCore R)) J u :=
    fun c hc _ hy => conj_mem_linkLayerAt hΩ.conjInvariant hc
      (mem_normalizer_iff_conjSub_eq.mp (h.tight J hJ.1 u hu hc)) hy
  have hwt' : w ≠ t := fun h' => hwE (h' ▸ htE)
  have hwu' : w ≠ u := fun h' => hwE (h' ▸ huE)
  refine ⟨hBe, hB8, fun c hcB hc1 => ?_⟩
  rcases mem_closure_three_cases hw2 hwt.symm hwu.symm hcB with hcE | ⟨e', he', hce⟩
  ·
    rcases TypeCSetup.mem_closure_pair ht.sq hu.sq ctu hcE with h1 | h1 | h1 | h1
    · exact absurd h1 hc1
    · rw [h1]
      exact hyp51At_of_forall_not (not_movedByAll_of_layer linkLayerAt_le_centralizer
        (fun _ hc _ hy => conj_mem_linkLayer hL hc hy) hBe htB ht.ne_one huB hu.ne_one
        htu.symm huΛ hwB hw1 hwt' htrivt)
    · rw [h1]
      exact hyp51At_of_forall_not (not_movedByAll_of_layer linkLayerAt_le_centralizer hNu hBe
        huB hu.ne_one htB ht.ne_one htu htΛ hwB hw1 hwu' htrivu)
    · rw [h1]
      exact hyp51At_mul_of_edge h4 htw hOm hL hJ hu hBe htB huB
  subst hce
  exact hyp51At_wcoset h4 h5 htw hE4 hL hJ hu hwt hwu hBe hBelow hcent hEB he' hwB hc1 hwE hR₀
    hR₀u hR₀w hT₀ hT₀N hT₀w

end Frame

end LinkZ2A

end CFSG.ClassicalInvolution.Q3.TL4
