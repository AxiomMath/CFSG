module

public import CFSG.LocalAnalysis.ComponentClassification.GS82L34G1Layer
public import CFSG.LocalAnalysis.ComponentClassification.GS82HConfigCtx
public import CFSG.GH74.GLS.C3.Layer1.Defs
public import CFSG.GH74.Generic.BProg.LBalanceNested
public import CFSG.GH74.Generic.BProg.B3.S3Ctx29Layer
public import CFSG.GH74.GLS.Stage2.Signalizer.L52TwoI1Basic
public import CFSG.GH74.GLS.TwoThin.Bridge
public import CFSG.LocalAnalysis.ComponentClassification.TwoLayerTransport
public import CFSG.LocalAnalysis.ComponentClassification.OuterAutomorphisms
public import CFSG.LocalAnalysis.ComponentInitial.LinearCoverModel
public import Certificates.Kernel.ThCent.Leaves
public import CFSG.GH74.Generic.BProg.B3.S3Ctx29

public section

namespace CFSG.ComponentClassification.GSThmB

namespace L34OmegaAux

open CFSG Subgroup CFSG.GH74.GLS CFSG.LocalAnalysis.ComponentInitial.LinearFlag

variable {G : Type} [Group G]

@[expose] noncomputable def slCongr {n : ℕ} {K K' : Type*} [Field K] [Field K'] (e : K ≃+* K') :
    Matrix.SpecialLinearGroup (Fin n) K ≃* Matrix.SpecialLinearGroup (Fin n) K' where
  toFun := Matrix.SpecialLinearGroup.map e.toRingHom
  invFun := Matrix.SpecialLinearGroup.map e.symm.toRingHom
  left_inv g := by
    ext i j
    simp
  right_inv g := by
    ext i j
    simp
  map_mul' := map_mul _

@[expose] noncomputable def projectiveSLCongr {n : ℕ} {K K' : Type*} [Field K] [Field K'] (e : K ≃+* K') :
    projectiveSL n K ≃* projectiveSL n K' :=
  QuotientGroup.congr (scalars n K) (scalars n K') (slCongr e) (by
    rw [scalars_eq_center, scalars_eq_center]
    exact CFSG.ComponentClassification.OuterAutomorphisms.center_map_equiv (slCongr e))

@[expose] def conjSub (L : Subgroup G) (g : G) (hg : g ∈ normalizer (L : Set G)) : ↥L ≃* ↥L where
  toFun x := ⟨g * x * g⁻¹, (mem_normalizer_iff.mp hg x).mp x.2⟩
  invFun x := ⟨g⁻¹ * x * g, by
    have h := (mem_normalizer_iff.mp (inv_mem hg) x).mp x.2
    rwa [inv_inv] at h⟩
  left_inv x := by ext; simp [mul_assoc]
  right_inv x := by ext; simp [mul_assoc]
  map_mul' x y := by ext; simp [mul_assoc]

@[expose] noncomputable def barAut (L : Subgroup G) (g : G) (hg : g ∈ normalizer (L : Set G)) :
    MulAut (↥L ⧸ pPrimeCore 2 ↥L) :=
  QuotientGroup.congr (pPrimeCore 2 ↥L) (pPrimeCore 2 ↥L) (conjSub L g hg)
    (pPrimeCore_map_iso 2 (conjSub L g hg))

theorem barAut_mk (L : Subgroup G) (g : G) (hg : g ∈ normalizer (L : Set G)) (y : ↥L) :
    barAut L g hg (QuotientGroup.mk' (pPrimeCore 2 ↥L) y) =
      QuotientGroup.mk' (pPrimeCore 2 ↥L) ⟨g * y * g⁻¹, (mem_normalizer_iff.mp hg y).mp y.2⟩ :=
  rfl

@[expose] noncomputable def psi {P : Type} [Group P] (L : Subgroup G) (t : G)
    (φ : ↥L ⧸ pPrimeCore 2 ↥L ≃* P) : ↥(L ⊓ centralizer ({t} : Set G)) →* P :=
  φ.toMonoidHom.comp ((QuotientGroup.mk' (pPrimeCore 2 ↥L)).comp (Subgroup.inclusion inf_le_left))

theorem psi_apply {P : Type} [Group P] (L : Subgroup G) (t : G)
    (φ : ↥L ⧸ pPrimeCore 2 ↥L ≃* P) (q : ↥(L ⊓ centralizer ({t} : Set G))) :
    psi L t φ q = φ (QuotientGroup.mk' (pPrimeCore 2 ↥L) ⟨q, q.2.1⟩) :=
  rfl

theorem conj_mem_pPrimeCoreOf [Finite G] {Λ : Subgroup G} {g n : G} (hg : g ∈ Λ)
    (hn : n ∈ pPrimeCoreOf 2 Λ) : g * n * g⁻¹ ∈ pPrimeCoreOf 2 Λ :=
  (mem_normalizer_iff.mp (TwoThin.mem_normalizer_pPrimeCoreOf (le_normalizer hg)) n).mp hn

variable [Finite G]

theorem exists_mul_comm_of_odd {Λ O : Subgroup G} (hOΛ : O ≤ Λ)
    (hodd : Odd (Nat.card O)) {c : G} (hc2 : c * c = 1) {y : G} (hy : y ∈ Λ)
    (hn : y⁻¹ * (c⁻¹ * y * c) ∈ O) :
    ∃ m ∈ O, y * m ∈ Λ ∧ c * (y * m) = (y * m) * c := by
  set n := y⁻¹ * (c⁻¹ * y * c) with hndef
  have hci : c⁻¹ = c := (eq_inv_of_mul_eq_one_left hc2).symm
  have hk : Odd (orderOf n) := Odd.of_dvd_nat hodd (Subgroup.orderOf_dvd_natCard O hn)
  set m := n ^ ((orderOf n + 1) / 2) with hmdef
  have hmO : m ∈ O := pow_mem hn _
  have hmm : m * m = n := by
    rw [hmdef, ← pow_two, ← pow_mul]
    have : (orderOf n + 1) / 2 * 2 = orderOf n + 1 :=
      Nat.div_mul_cancel (even_iff_two_dvd.mp hk.add_one)
    rw [this, pow_succ, pow_orderOf_eq_one, one_mul]
  have hcn : c⁻¹ * n * c = n⁻¹ := by
    rw [hndef]
    calc c⁻¹ * (y⁻¹ * (c⁻¹ * y * c)) * c = c⁻¹ * y⁻¹ * c⁻¹ * y * (c * c) := by group
      _ = c⁻¹ * y⁻¹ * c⁻¹ * y := by rw [hc2, mul_one]
      _ = (y⁻¹ * (c⁻¹ * y * c))⁻¹ := by simp only [mul_inv_rev, inv_inv, hci, mul_assoc]
  have hcm : c⁻¹ * m * c = m⁻¹ := by
    have h := map_pow (MulAut.conj c⁻¹) n ((orderOf n + 1) / 2)
    simp only [MulAut.conj_apply, inv_inv] at h
    rw [hmdef, h, hcn, inv_pow]
  have hcy : c⁻¹ * y * c = y * n := by rw [hndef]; group
  refine ⟨m, hmO, mul_mem hy (hOΛ hmO), ?_⟩
  have hfix : c⁻¹ * (y * m) * c = y * m := by
    calc c⁻¹ * (y * m) * c = (c⁻¹ * y * c) * (c⁻¹ * m * c) := by group
      _ = y * (m * m) * m⁻¹ := by rw [hcy, hcm, hmm]
      _ = y * m := by group
  calc c * (y * m) = c * (c⁻¹ * (y * m) * c) := by rw [hfix]
    _ = (y * m) * c := by group

theorem orderOf_mk_eq_two (L : Subgroup G) {t : G} (htL : t ∈ L) (ht : orderOf t = 2) :
    orderOf (QuotientGroup.mk' (pPrimeCore 2 ↥L) (⟨t, htL⟩ : ↥L)) = 2 := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have ht' : orderOf (⟨t, htL⟩ : ↥L) = 2 := by rw [Subgroup.orderOf_mk]; exact ht
  refine orderOf_eq_prime ?_ ?_
  · rw [← map_pow, ← ht', pow_orderOf_eq_one, map_one]
  · intro h
    rw [QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff] at h
    have h1 := Subgroup.orderOf_dvd_natCard _ h
    rw [ht'] at h1
    exact (Nat.not_even_iff_odd.mpr (TwoThin.odd_card_pPrimeCore ↥L)) (even_iff_two_dvd.mpr h1)

theorem layer_image {P : Type} [Group P] [Finite P] (L : Subgroup G) {t : G} (htL : t ∈ L)
    (ht2 : t * t = 1) (φ : ↥L ⧸ pPrimeCore 2 ↥L ≃* P) :
    pLayerOf 2 (centralizer ({φ (QuotientGroup.mk' (pPrimeCore 2 ↥L) ⟨t, htL⟩)} : Set P)) =
      (ComponentClassification.TwoLayer.subgroup ↥(L ⊓ centralizer ({t} : Set G))).map
        (psi L t φ) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  set Q := L ⊓ centralizer ({t} : Set G) with hQ
  set π := QuotientGroup.mk' (pPrimeCore 2 ↥L) with hπ
  set i := φ (π ⟨t, htL⟩) with hi
  set Z := centralizer ({i} : Set P) with hZ
  have hQL : Q ≤ L := inf_le_left
  have hrange : ∀ q : ↥Q, psi L t φ q ∈ Z := by
    intro q
    rw [hZ, mem_centralizer_singleton_iff, psi_apply, hi, ← map_mul, ← map_mul, ← map_mul,
      ← map_mul]
    congr 2
    have h := mem_centralizer_singleton_iff.mp q.2.2
    first
      | exact Subtype.ext h
      | exact Subtype.ext h.symm
  set Ψ : ↥Q →* ↥Z := (psi L t φ).codRestrict Z hrange with hΨ
  have hsurj : Function.Surjective Ψ := by
    rintro ⟨z, hz⟩
    obtain ⟨u, rfl⟩ := φ.surjective z
    obtain ⟨y, rfl⟩ := QuotientGroup.mk'_surjective (pPrimeCore 2 ↥L) u
    have hcomm : π y * π ⟨t, htL⟩ = π ⟨t, htL⟩ * π y := by
      have h := mem_centralizer_singleton_iff.mp hz
      apply φ.injective
      rw [map_mul, map_mul]
      first
        | exact h
        | exact h.symm
    have h2 : π y = π ((⟨t, htL⟩ : ↥L)⁻¹ * y * ⟨t, htL⟩) := by
      rw [map_mul, map_mul, map_inv, mul_assoc, hcomm, ← mul_assoc, inv_mul_cancel, one_mul]
    rw [hπ, QuotientGroup.mk'_apply, QuotientGroup.mk'_apply, QuotientGroup.eq] at h2
    have hn : (y : G)⁻¹ * (t⁻¹ * y * t) ∈ pPrimeCoreOf 2 L :=
      (Stage2.Signalizer.L52Two.I1.mem_pPrimeCoreOf_iff _).2 h2
    obtain ⟨m, hmO, hym, hcomm'⟩ := exists_mul_comm_of_odd (TwoThin.pPrimeCoreOf_le L)
      (TwoThin.card_pPrimeCoreOf_odd L) ht2 y.2 hn
    have hq : (y : G) * m ∈ Q := by
      refine ⟨hym, mem_centralizer_singleton_iff.mpr ?_⟩
      first
        | exact hcomm'
        | exact hcomm'.symm
    refine ⟨⟨_, hq⟩, ?_⟩
    apply Subtype.ext
    show φ (π ⟨(y : G) * m, hym⟩) = φ (π y)
    congr 1
    rw [hπ, QuotientGroup.mk'_apply, QuotientGroup.mk'_apply, QuotientGroup.eq]
    have hm' : (⟨m⁻¹, TwoThin.pPrimeCoreOf_le L (inv_mem hmO)⟩ : ↥L) ∈ pPrimeCore 2 ↥L :=
      (Stage2.Signalizer.L52Two.I1.mem_pPrimeCoreOf_iff _).1 (inv_mem hmO)
    convert hm' using 1
    ext
    simp
  have hodd : Odd (Nat.card Ψ.ker) := by
    have hk : Ψ.ker ≤ (pPrimeCore 2 ↥L).comap (Subgroup.inclusion hQL) := by
      intro x hx
      rw [MonoidHom.mem_ker] at hx
      have hx' : φ (π (Subgroup.inclusion hQL x)) = 1 := congrArg Subtype.val hx
      rw [MulEquiv.map_eq_one_iff, hπ, QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff] at hx'
      exact hx'
    exact Odd.of_dvd_nat (TwoThin.odd_card_pPrimeCore ↥L) ((Subgroup.card_dvd_of_le hk).trans
      (Subgroup.card_comap_dvd_of_injective _ _ (Subgroup.inclusion_injective hQL)))
  have himg := ComponentClassification.TwoLayerTransport.image_of_odd_kernel Ψ hsurj hodd
  rw [TwoThin.pLayerOf_two_eq_map, ← himg, Subgroup.map_map]
  rfl

theorem map_eq_one_of_odd_normal {A P : Type} [Group A] [Finite A] [Group P] [Finite P]
    (f : A →* P) {S W : Subgroup A} (hWS : W ≤ S) (hW : (W.subgroupOf S).Normal)
    (hodd : Odd (Nat.card W)) (hcore : pPrimeCore 2 ↥(S.map f) = ⊥) {w : A} (hw : w ∈ W) :
    f w = 1 := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  set M : Subgroup ↥(S.map f) := (W.subgroupOf S).map (f.subgroupMap S) with hM
  have hMn : M.Normal := hW.map _ (f.subgroupMap_surjective S)
  have hMc : Nat.Coprime 2 (Nat.card M) := by
    rw [Nat.coprime_two_left]
    refine Odd.of_dvd_nat hodd ((Subgroup.card_map_dvd _ _).trans ?_)
    rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe hWS).toEquiv]
  have hle : M ≤ pPrimeCore 2 ↥(S.map f) := le_sSup ⟨hMn, hMc⟩
  rw [hcore] at hle
  have h1 : f.subgroupMap S ⟨w, hWS hw⟩ ∈ M := ⟨⟨w, hWS hw⟩, mem_subgroupOf.mpr hw, rfl⟩
  have h2 := hle h1
  rw [Subgroup.mem_bot] at h2
  exact congrArg Subtype.val h2

end L34OmegaAux

open L34DP
open CFSG Subgroup CFSG.LocalAnalysis.ComponentInitial.LinearFlag
open scoped MatrixGroups

variable {X : Type} [Group X] [Finite X]

theorem Eight2.CtxA0.lemmaOmega_of
    (c : Eight2.CtxA0 X)
    (hA : ¬ Nonempty (↥(generalizedFitting (c.s.h.subQuot c.s.y)) ≃* alternatingGroup (Fin 10)))
    (hq7 : c.s.p ^ c.s.f = 7) (ω : X)
    (hG1 : ∀ i : projectiveSL 4 (ZMod 7), orderOf i = 2 →
      i ∈ GH74.GLS.pLayerOf 2 (centralizer ({i} : Set (projectiveSL 4 (ZMod 7)))) →
      ∃ g, g * i * g⁻¹ = proj 4 (ZMod 7) dSL)
    (hG2 : GH74.GLS.pLayerOf 2 (centralizer ({proj 4 (ZMod 7) dSL} :
      Set (projectiveSL 4 (ZMod 7)))) = blockImage ∧ pPrimeCore 2 ↥blockImage = ⊥)
    (hG3 : ∀ α : MulAut (projectiveSL 4 (ZMod 7)),
      (∀ a b : SL(2, ZMod 7), α (proj 4 (ZMod 7) (blk a b)) = proj 4 (ZMod 7) (blk a b)) →
      α * α ≠ MulAut.conj (proj 4 (ZMod 7) dSL))
    (hωB : ω ∈ centralizer (c.s.h.secB0 c.s.y : Set X))
    (hω2 : ω ^ 2 = c.s.h.a * c.b * c.Z.z) (hω : ∃ n : ℕ, ω ^ 2 ^ n = 1)
    (hωc : ∀ y ∈ GH74.GLS.pLayerOf 2 (centralizer ({c.s.h.a * c.b * c.Z.z} : Set X)),
      y⁻¹ * (ω⁻¹ * y * ω) ∈
        GH74.GLS.pPrimeCoreOf 2 (centralizer ({c.s.h.a * c.b * c.Z.z} : Set X))) :
    False := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hq3 : ¬ (c.s.p = 3 ∧ c.s.f = 1) := by
    rintro ⟨h1, h2⟩
    rw [h1, h2] at hq7
    norm_num at hq7
  obtain ⟨N₁, hN₁le, hN₁c, htN₁, -⟩ :=
    gs82Step6ProdInputA0_of_cf CatFactsL4U4.cfL4U4Prod X c hA hq3
  set t := c.s.h.a * c.b * c.Z.z with ht_def
  set C := centralizer (c.s.h.secB0 c.s.y : Set X) with hC
  set L := Seven.Lay c.s.h c.s.y with hL
  set Y := centralizer ({t} : Set X) with hY
  set Q := L ⊓ Y with hQ
  set E := GH74.GLS.pLayerOf 2 Q with hE
  have ht : orderOf t = 2 := c.orderOf_abz
  have ht2 : t * t = 1 := by rw [← pow_two, ← ht, pow_orderOf_eq_one]
  have htL : t ∈ L := c.delta_mem_Lay
  have hLC : L ≤ C := Seven.Lay_le_centralizer_secB0 c.s.h c.s.y
  have hCN : C ≤ normalizer (L : Set X) :=
    (normal_subgroupOf_iff_le_normalizer hLC).mp (Seven.normal_layerIn_subgroupOf C)
  have hωω : ω * ω = t := by rw [← pow_two, hω2]
  have hωY : ω ∈ Y := by
    rw [hY, mem_centralizer_singleton_iff, ← hωω, mul_assoc]
  have hωL : ω ∈ normalizer (L : Set X) := hCN hωB
  have hωQ : ω ∈ normalizer (Q : Set X) := by
    rw [mem_normalizer_iff]
    intro x
    rw [hQ, mem_inf, mem_inf, ← mem_normalizer_iff.mp hωL x,
      ← mem_normalizer_iff.mp (le_normalizer hωY) x]
  have hωE : ω ∈ normalizer (E : Set X) :=
    GH74.Generic.BProg.B3.S3Ctx29Layer.mem_normalizer_pLayerOf_of_mem_normalizer hωQ
  have hB₀Y : c.s.h.secB0 c.s.y ≤ Y := fun b hb =>
    mem_centralizer_singleton_iff.mpr (mem_centralizer_iff.mp (hLC htL) b hb)
  have hEΛ : E ≤ GH74.GLS.pLayerOf 2 Y := by
    have hQM : Q ≤ Y ⊓ C := fun x hx => ⟨hx.2, hLC hx.1⟩
    have : (Q.subgroupOf (Y ⊓ C)).Normal := by
      refine (normal_subgroupOf_iff_le_normalizer hQM).mpr fun g hg => ?_
      rw [mem_normalizer_iff]
      intro x
      rw [hQ, mem_inf, mem_inf, ← mem_normalizer_iff.mp (hCN (mem_inf.mp hg).2) x,
        ← mem_normalizer_iff.mp (le_normalizer (mem_inf.mp hg).1) x]
    exact (GH74.Generic.BProg.pLayerOf_le_of_normal 2 hQM).trans
      (GH74.GLS.Stage2.Signalizer.L52Two.I1.pLayerOf_inf_centralizer_le hB₀Y
        (c.s.h.isPGroup_secB0 c.s.y))
  have htE : t ∈ E := (le_sSup ⟨hN₁le, hN₁c⟩ : N₁ ≤ E) htN₁
  have htQ : t ∈ Q := ⟨htL, mem_centralizer_singleton_iff.mpr rfl⟩
  have htTL : (⟨t, htQ⟩ : ↥Q) ∈ ComponentClassification.TwoLayer.subgroup ↥Q := by
    have h1 := htE
    rw [hE, GH74.GLS.TwoThin.pLayerOf_two_eq_map] at h1
    obtain ⟨w, hw, hwt⟩ := h1
    rwa [show w = ⟨t, htQ⟩ from Subtype.ext hwt] at hw
  obtain ⟨φ₀⟩ : Nonempty (↥L ⧸ pPrimeCore 2 ↥L ≃* projectiveSL 4 (ZMod 7)) := by
    rcases c.lieModel_Lay hA with ⟨hlie, -⟩ | ⟨-, h4⟩
    · obtain ⟨K, _, _, hK, ⟨e⟩⟩ :=
        LocalAnalysis.ComponentInitial.LinearCover.exists_mulEquiv_projectiveSL_of_lieModel hlie
      have : Fintype K := Fintype.ofFinite K
      have hK' : Fintype.card K = 7 := by rw [← Nat.card_eq_fintype_card, hK, hq7]
      have : Fact (Nat.Prime 7) := ⟨by norm_num⟩
      have : CharP K 7 := charP_of_card_eq_prime hK'
      exact ⟨e.trans (L34OmegaAux.projectiveSLCongr (ZMod.ringEquiv K hK').symm)⟩
    · rw [hq7] at h4
      norm_num at h4
  set i₀ := φ₀ (QuotientGroup.mk' (pPrimeCore 2 ↥L) ⟨t, htL⟩) with hi₀
  have hi₀2 : orderOf i₀ = 2 := by
    rw [hi₀, MulEquiv.orderOf_eq]
    exact L34OmegaAux.orderOf_mk_eq_two L htL ht
  have hi₀L : i₀ ∈ GH74.GLS.pLayerOf 2 (centralizer ({i₀} : Set (projectiveSL 4 (ZMod 7)))) := by
    rw [hi₀, L34OmegaAux.layer_image L htL ht2 φ₀]
    exact ⟨_, htTL, rfl⟩
  obtain ⟨g, hg⟩ := hG1 i₀ hi₀2 hi₀L
  set φ := φ₀.trans (MulAut.conj g) with hφ
  have hφt : φ (QuotientGroup.mk' (pPrimeCore 2 ↥L) ⟨t, htL⟩) = proj 4 (ZMod 7) dSL := by
    rw [← hg]
    rfl
  have hlay := L34OmegaAux.layer_image L htL ht2 φ
  rw [hφt, hG2.1] at hlay
  set α : MulAut (projectiveSL 4 (ZMod 7)) :=
    (φ.symm.trans (L34OmegaAux.barAut L ω hωL)).trans φ with hα
  refine hG3 α ?_ ?_
  ·
    intro a b
    have hx : proj 4 (ZMod 7) (blk a b) ∈ blockImage := subset_closure ⟨(a, b), rfl⟩
    rw [hlay] at hx
    obtain ⟨q, hq, hqx⟩ := hx
    rw [← hqx]
    have hqE : (q : X) ∈ E := by
      rw [hE, GH74.GLS.TwoThin.pLayerOf_two_eq_map]
      exact ⟨q, hq, rfl⟩
    have hq'E : ω * q * ω⁻¹ ∈ E := (mem_normalizer_iff.mp hωE q).mp hqE
    have hq'Q : ω * q * ω⁻¹ ∈ Q := (mem_normalizer_iff.mp hωQ q).mp q.2
    set q' : ↥Q := ⟨ω * q * ω⁻¹, hq'Q⟩ with hq'
    have hq'T : q' ∈ ComponentClassification.TwoLayer.subgroup ↥Q := by
      have h1 := hq'E
      rw [hE, GH74.GLS.TwoThin.pLayerOf_two_eq_map] at h1
      obtain ⟨w, hw, hwq⟩ := h1
      rwa [show w = q' from Subtype.ext hwq] at hw
    have hαq : α (L34OmegaAux.psi L t φ q) = L34OmegaAux.psi L t φ q' := by
      simp only [hα, MulEquiv.trans_apply, L34OmegaAux.psi_apply, MulEquiv.symm_apply_apply,
        L34OmegaAux.barAut_mk]
      rfl
    rw [hαq]
    set W : Subgroup ↥Q := (GH74.GLS.pPrimeCoreOf 2 Y).comap Q.subtype ⊓
      ComponentClassification.TwoLayer.subgroup ↥Q with hW
    have hWn : (W.subgroupOf (ComponentClassification.TwoLayer.subgroup ↥Q)).Normal := by
      constructor
      intro n hn s
      rw [mem_subgroupOf] at hn ⊢
      obtain ⟨hn1, hn2⟩ := mem_inf.mp hn
      refine mem_inf.mpr ⟨?_, ?_⟩
      · rw [mem_comap] at hn1 ⊢
        simpa using L34OmegaAux.conj_mem_pPrimeCoreOf (s : ↥Q).2.2 hn1
      · exact mul_mem (mul_mem s.2 hn2) (inv_mem s.2)
    have hWodd : Odd (Nat.card W) :=
      Odd.of_dvd_nat (GH74.GLS.TwoThin.card_pPrimeCoreOf_odd Y)
        ((Subgroup.card_dvd_of_le inf_le_left).trans
          (Subgroup.card_comap_dvd_of_injective _ _ Q.subtype_injective))
    have hn : q'⁻¹ * q ∈ W := by
      refine mem_inf.mpr ⟨?_, mul_mem (inv_mem hq'T) hq⟩
      rw [mem_comap]
      have h1 := hωc _ (hEΛ hq'E)
      convert h1 using 1
      simp only [hq', Subgroup.coe_subtype, Subgroup.coe_mul, Subgroup.coe_inv]
      group
    have h1 := L34OmegaAux.map_eq_one_of_odd_normal (L34OmegaAux.psi L t φ) inf_le_right hWn hWodd
      (by rw [← hlay]; exact hG2.2) hn
    rw [map_mul, map_inv, inv_mul_eq_one] at h1
    exact h1
  ·
    ext x
    obtain ⟨z, rfl⟩ := φ.surjective x
    obtain ⟨y, rfl⟩ := QuotientGroup.mk'_surjective (pPrimeCore 2 ↥L) z
    rw [MulAut.mul_apply, MulAut.conj_apply, ← hφt]
    simp only [hα, MulEquiv.trans_apply, MulEquiv.symm_apply_apply, L34OmegaAux.barAut_mk]
    rw [← map_inv, ← map_mul, ← map_mul, ← map_inv, ← map_mul, ← map_mul]
    congr 2
    ext
    simp only [Subgroup.coe_mul, Subgroup.coe_inv]
    rw [← hωω]
    group

theorem Eight2.CtxA0.lemmaOmega
    (c : Eight2.CtxA0 X)
    (hA : ¬ Nonempty (↥(generalizedFitting (c.s.h.subQuot c.s.y)) ≃* alternatingGroup (Fin 10)))
    (hq7 : c.s.p ^ c.s.f = 7) (ω : X)
    (hωB : ω ∈ centralizer (c.s.h.secB0 c.s.y : Set X))
    (hω2 : ω ^ 2 = c.s.h.a * c.b * c.Z.z) (hω : ∃ n : ℕ, ω ^ 2 ^ n = 1)
    (hωc : ∀ y ∈ GH74.GLS.pLayerOf 2 (centralizer ({c.s.h.a * c.b * c.Z.z} : Set X)),
      y⁻¹ * (ω⁻¹ * y * ω) ∈
        GH74.GLS.pPrimeCoreOf 2 (centralizer ({c.s.h.a * c.b * c.Z.z} : Set X))) :
    False :=
  c.lemmaOmega_of hA hq7 ω L34DP.g1_class L34DP.g1_layer L34DP.g1_no_sqrt hωB hω2 hω hωc

end CFSG.ComponentClassification.GSThmB
