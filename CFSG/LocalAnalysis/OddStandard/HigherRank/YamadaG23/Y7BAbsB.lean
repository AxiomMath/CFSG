module

public import CFSG.LocalAnalysis.OddStandard.HigherRank.G2Three.FrameDefs

public section

namespace CFSG.OddStandard.HigherRank.YamadaG23

open Subgroup CFSG.Open CFSG.OddStandard.HigherRank.G2Three
  CFSG.OddStandard.HigherRank.G2Three.Sec1
open scoped commutatorElement

variable {G : Type} [Group G] [Finite G]

private theorem relIndex_sup_eq_of_le_normalizer {D T : Subgroup G}
    (hT : T ≤ Subgroup.normalizer (D : Set G)) : D.relIndex (T ⊔ D) = D.relIndex T := by
  have := Subgroup.normal_subgroupOf_of_le_normalizer hT
  have := Subgroup.normal_subgroupOf_sup_of_le_normalizer hT
  exact Nat.card_congr (QuotientGroup.quotientInfEquivProdNormalizerQuotient T D hT).toEquiv.symm

theorem card_sup_mul_card_inf_of_le_normalizer {H K : Subgroup G}
    (h : H ≤ normalizer (K : Set G)) :
    Nat.card ↥(H ⊔ K) * Nat.card ↥(H ⊓ K) = Nat.card ↥H * Nat.card ↥K := by
  have h1 : K.relIndex (H ⊔ K) * Nat.card ↥(K ⊓ (H ⊔ K)) = Nat.card ↥(H ⊔ K) :=
    Subgroup.relIndex_mul_card (H := K) (K := H ⊔ K)
  rw [inf_of_le_left le_sup_right] at h1
  have h2 : (H ⊓ K).relIndex H * Nat.card ↥((H ⊓ K) ⊓ H) = Nat.card ↥H :=
    Subgroup.relIndex_mul_card (H := H ⊓ K) (K := H)
  rw [inf_of_le_left inf_le_left] at h2
  have h3 : K.relIndex (H ⊔ K) = (H ⊓ K).relIndex H := by
    rw [relIndex_sup_eq_of_le_normalizer h, Subgroup.inf_relIndex_left]
  calc Nat.card ↥(H ⊔ K) * Nat.card ↥(H ⊓ K)
      = (K.relIndex (H ⊔ K) * Nat.card ↥K) * Nat.card ↥(H ⊓ K) := by rw [h1]
    _ = Nat.card ↥K * ((H ⊓ K).relIndex H * Nat.card ↥(H ⊓ K)) := by rw [h3]; ring
    _ = Nat.card ↥K * Nat.card ↥H := by rw [h2]
    _ = Nat.card ↥H * Nat.card ↥K := by ring

theorem mem_sup_iff_exists_mul_of_le_normalizer {H K : Subgroup G}
    (h : H ≤ normalizer (K : Set G)) {x : G} :
    x ∈ H ⊔ K ↔ ∃ a ∈ H, ∃ b ∈ K, x = a * b := by
  change x ∈ (↑(H ⊔ K) : Set G) ↔ ∃ a ∈ H, ∃ b ∈ K, x = a * b
  rw [Subgroup.coe_mul_of_left_le_normalizer_right H K h, Set.mem_mul]
  constructor
  · rintro ⟨a, ha, b, hb, hab⟩; exact ⟨a, ha, b, hb, hab.symm⟩
  · rintro ⟨a, ha, b, hb, rfl⟩; exact ⟨a, ha, b, hb, rfl⟩

theorem mem_sup_iff_exists_mul_of_le_normalizer' {H K : Subgroup G}
    (h : H ≤ normalizer (K : Set G)) {x : G} :
    x ∈ H ⊔ K ↔ ∃ b ∈ K, ∃ a ∈ H, x = b * a := by
  rw [sup_comm]
  change x ∈ (↑(K ⊔ H) : Set G) ↔ ∃ b ∈ K, ∃ a ∈ H, x = b * a
  rw [Subgroup.coe_mul_of_right_le_normalizer_left K H h, Set.mem_mul]
  constructor
  · rintro ⟨b, hb, a, ha, hba⟩; exact ⟨b, hb, a, ha, hba.symm⟩
  · rintro ⟨b, hb, a, ha, rfl⟩; exact ⟨b, hb, a, ha, rfl⟩

theorem mem_of_comm_mem_of_relIndex_sq {M V Y : Subgroup G} {t : G} (htt : t * t = 1)
    (hVM : V ≤ M) (hMc : ∀ m ∈ M, ∀ n ∈ M, ⁅m, n⁆ ∈ V) (hMsq : ∀ m ∈ M, m ^ 2 ∈ V)
    (htM : ∀ m ∈ M, t * m * t⁻¹ ∈ M) (htV : ∀ v ∈ V, t * v * t⁻¹ ∈ V)
    (hVY : V ≤ Y) (hYM : Y ≤ M) (hY : ∀ y ∈ Y, ⁅t, y⁆ ∈ V)
    (hYim : ∀ y ∈ Y, ∃ m ∈ M, y⁻¹ * ⁅m, t⁆ ∈ V) (hcard : V.relIndex M = (V.relIndex Y) ^ 2) :
    ∀ m ∈ M, ⁅t, m⁆ ∈ V → m ∈ Y := by
  let V' : Subgroup ↥M := V.subgroupOf M
  let Y' : Subgroup ↥M := Y.subgroupOf M
  have hV'Y' : V' ≤ Y' := fun x hx => hVY hx
  have hcomm_le : _root_.commutator ↥M ≤ V' := by
    rw [_root_.commutator_def, Subgroup.commutator_le]
    intro a _ b _
    show ⁅(a : G), (b : G)⁆ ∈ V
    exact hMc a a.2 b b.2
  have hV'normal : V'.Normal :=
    Subgroup.commutator_top_left_le_iff.mp
      ((Subgroup.commutator_mono le_rfl le_top).trans hcomm_le)
  haveI : V'.Normal := hV'normal
  haveI : IsMulCommutative (↥M ⧸ V') :=
    Subgroup.Normal.quotient_commutative_iff_commutator_le.mpr hcomm_le
  let mk : ↥M →* (↥M ⧸ V') := QuotientGroup.mk' V'
  let σM : ↥M →* ↥M := MonoidHom.mk'
    (fun m => ⟨t * (m : G) * t⁻¹, htM m m.2⟩)
    (by
      intro a b
      ext
      show t * ((a : G) * (b : G)) * t⁻¹ = t * (a : G) * t⁻¹ * (t * (b : G) * t⁻¹)
      group)
  have hσMV : ∀ v ∈ V', σM v ∈ V' := fun v hv => htV v hv
  have hσM2 : ∀ m : ↥M, σM (σM m) = m := by
    intro m
    ext
    show t * (t * (m : G) * t⁻¹) * t⁻¹ = (m : G)
    calc t * (t * (m : G) * t⁻¹) * t⁻¹ = (t * t) * (m : G) * (t⁻¹ * t⁻¹) := by group
      _ = (t * t) * (m : G) * (t * t)⁻¹ := by rw [← mul_inv_rev]
      _ = (m : G) := by rw [htt, inv_one, mul_one, one_mul]
  let σ : (↥M ⧸ V') →* (↥M ⧸ V') :=
    QuotientGroup.lift V' (mk.comp σM) (by
      intro v hv
      show mk (σM v) = 1
      exact (QuotientGroup.eq_one_iff (σM v)).mpr (hσMV v hv))
  have hσmk : ∀ m : ↥M, σ (mk m) = mk (σM m) := by
    intro m
    change QuotientGroup.lift V' (mk.comp σM) _ (QuotientGroup.mk m)
        = QuotientGroup.mk (σM m)
    rw [QuotientGroup.lift_mk]
    rfl
  let g : ↥M →* (↥M ⧸ V') := MonoidHom.mk'
    (fun m => mk (σM m) * (mk m)⁻¹)
    (by
      intro a b
      simp only [map_mul, mul_inv_rev]
      have hc : (mk (σM b) * (mk b)⁻¹) * (mk a)⁻¹
          = (mk a)⁻¹ * (mk (σM b) * (mk b)⁻¹) := mul_comm' _ _
      calc mk (σM a) * mk (σM b) * ((mk b)⁻¹ * (mk a)⁻¹)
          = mk (σM a) * ((mk (σM b) * (mk b)⁻¹) * (mk a)⁻¹) := by group
        _ = mk (σM a) * ((mk a)⁻¹ * (mk (σM b) * (mk b)⁻¹)) := by rw [hc]
        _ = mk (σM a) * (mk a)⁻¹ * (mk (σM b) * (mk b)⁻¹) := by group)
  let ψ : (↥M ⧸ V') →* (↥M ⧸ V') :=
    QuotientGroup.lift V' g (by
      intro v hv
      rw [MonoidHom.mem_ker]
      change mk (σM v) * (mk v)⁻¹ = 1
      have hmkv : mk v = 1 := (QuotientGroup.eq_one_iff v).mpr hv
      rw [hmkv, inv_one, mul_one]
      exact (QuotientGroup.eq_one_iff (σM v)).mpr (hσMV v hv))
  have hψmk : ∀ m : ↥M, ψ (mk m) = mk (σM m) * (mk m)⁻¹ := by
    intro m
    change QuotientGroup.lift V' g _ (QuotientGroup.mk m)
        = QuotientGroup.mk (σM m) * (QuotientGroup.mk m)⁻¹
    rw [QuotientGroup.lift_mk]
    rfl
  have hYVcard : Nat.card (Y'.map mk) = V.relIndex Y := by
    have h1 : V'.relIndex Y' = Nat.card (Y'.map mk) := by
      have := Subgroup.relIndex_ker mk (K := Y')
      rwa [QuotientGroup.ker_mk'] at this
    rw [← h1]
    exact Subgroup.relIndex_subgroupOf hYM
  set n := Nat.card (Y'.map mk) with hn
  have hnpos : 0 < n := by
    rw [hn]
    haveI : Nonempty (Y'.map mk) := ⟨1⟩
    exact Nat.card_pos
  have hYker : Y'.map mk ≤ ψ.ker := by
    intro a ha
    rw [Subgroup.mem_map] at ha
    obtain ⟨y, hy, rfl⟩ := ha
    rw [MonoidHom.mem_ker, hψmk]
    have hyV : σM y * y⁻¹ ∈ V' := by
      show t * (y : G) * t⁻¹ * (y : G)⁻¹ ∈ V
      have h : ⁅t, (y : G)⁆ ∈ V := hY (y : G) hy
      rwa [commutatorElement_def] at h
    rw [show mk (σM y) * (mk y)⁻¹ = mk (σM y * y⁻¹) by rw [← map_inv, ← map_mul]]
    exact (QuotientGroup.eq_one_iff (σM y * y⁻¹)).mpr hyV
  have hYrange : Y'.map mk ≤ ψ.range := by
    intro a ha
    rw [Subgroup.mem_map] at ha
    obtain ⟨y, hy, rfl⟩ := ha
    rw [MonoidHom.mem_range]
    obtain ⟨m, hm, hmy⟩ := hYim (y : G) hy
    refine ⟨mk (⟨m, hm⟩ : ↥M), ?_⟩
    have hmt_mem : ⁅m, t⁆ ∈ M := by
      have h1 : t * m * t⁻¹ ∈ M := htM m hm
      have he : ⁅m, t⁆ = m * (t * m * t⁻¹)⁻¹ := by rw [commutatorElement_def]; group
      rw [he]
      exact M.mul_mem hm (M.inv_mem h1)
    have hsq : (⟨⁅m, t⁆, hmt_mem⟩ : ↥M) ^ 2 ∈ V' := by
      show ⁅m, t⁆ ^ 2 ∈ V
      exact hMsq ⁅m, t⁆ hmt_mem
    have hinv : (σM (⟨m, hm⟩ : ↥M) * (⟨m, hm⟩ : ↥M)⁻¹)⁻¹
        = (⟨⁅m, t⁆, hmt_mem⟩ : ↥M) := by
      ext
      show (t * m * t⁻¹ * m⁻¹)⁻¹ = ⁅m, t⁆
      rw [commutatorElement_def]; group
    have heq1 : mk (σM (⟨m, hm⟩ : ↥M) * (⟨m, hm⟩ : ↥M)⁻¹)
        = mk (⟨⁅m, t⁆, hmt_mem⟩ : ↥M) := by
      change QuotientGroup.mk (σM (⟨m, hm⟩ : ↥M) * (⟨m, hm⟩ : ↥M)⁻¹)
        = QuotientGroup.mk (⟨⁅m, t⁆, hmt_mem⟩ : ↥M)
      rw [QuotientGroup.eq, hinv, ← pow_two]
      exact hsq
    have heq2 : mk y = mk (⟨⁅m, t⁆, hmt_mem⟩ : ↥M) := by
      change QuotientGroup.mk y = QuotientGroup.mk (⟨⁅m, t⁆, hmt_mem⟩ : ↥M)
      rw [QuotientGroup.eq]
      show (y : G)⁻¹ * ⁅m, t⁆ ∈ V
      exact hmy
    rw [hψmk]
    rw [show mk (σM (⟨m, hm⟩ : ↥M)) * (mk (⟨m, hm⟩ : ↥M))⁻¹
          = mk (σM (⟨m, hm⟩ : ↥M) * (⟨m, hm⟩ : ↥M)⁻¹) by rw [← map_inv, ← map_mul]]
    rw [heq1, heq2]
  have hA2 : ∀ a : (↥M ⧸ V'), a ^ 2 = 1 := by
    intro a
    refine QuotientGroup.induction_on a fun m => ?_
    change (mk m) ^ 2 = 1
    have hm2 : m ^ 2 ∈ V' := by
      show (m : G) ^ 2 ∈ V
      exact hMsq m m.2
    rw [← map_pow]
    exact (QuotientGroup.eq_one_iff (m ^ 2)).mpr hm2
  have hAinv : ∀ a : (↥M ⧸ V'), a⁻¹ = a := by
    intro a
    have h := hA2 a
    rw [pow_two] at h
    exact (mul_eq_one_iff_eq_inv.mp h).symm
  have hσ2' : ∀ a : (↥M ⧸ V'), σ (σ a) = a := by
    intro a
    refine QuotientGroup.induction_on a fun m => ?_
    change σ (σ (mk m)) = mk m
    rw [hσmk, hσmk, hσM2]
  have hψeq : ∀ a : (↥M ⧸ V'), ψ a = σ a * a⁻¹ := by
    intro a
    refine QuotientGroup.induction_on a fun m => ?_
    change ψ (mk m) = σ (mk m) * (mk m)⁻¹
    rw [hψmk, hσmk]
  have hψψ : ∀ a : (↥M ⧸ V'), ψ (ψ a) = 1 := by
    intro a
    rw [hψeq (ψ a), hψeq a]
    rw [map_mul, map_inv, hσ2' a, mul_inv_rev, inv_inv, ← pow_two]
    exact hA2 _
  have him_le_ker : ψ.range ≤ ψ.ker := by
    intro x hx
    rw [MonoidHom.mem_range] at hx
    obtain ⟨a, rfl⟩ := hx
    rw [MonoidHom.mem_ker]
    exact hψψ a
  have hcardψ := Subgroup.card_ker_mul_card_range ψ
  have hcardA : Nat.card (↥M ⧸ V') = V.relIndex M := rfl
  have hrange_le : Nat.card ψ.range ≤ Nat.card ψ.ker := Subgroup.card_le_of_le him_le_ker
  have hYrange_le : Nat.card (Y'.map mk) ≤ Nat.card ψ.range := Subgroup.card_le_of_le hYrange
  have hYker_le : Nat.card (Y'.map mk) ≤ Nat.card ψ.ker := hYrange_le.trans hrange_le
  have hprod : Nat.card ψ.ker * Nat.card ψ.range = n * n := by
    rw [hcardψ, hcardA, hcard, ← hYVcard, pow_two]
  have hrange_eq : Nat.card ψ.range = n := by
    have h1 : n * n ≤ n * Nat.card ψ.range := Nat.mul_le_mul_left n hYrange_le
    have h2 : n * Nat.card ψ.range ≤ n * Nat.card ψ.ker := Nat.mul_le_mul_left n hrange_le
    have h3 : n * Nat.card ψ.ker ≤ Nat.card ψ.range * Nat.card ψ.ker :=
      Nat.mul_le_mul_right _ hYrange_le
    have h4 : Nat.card ψ.range * Nat.card ψ.ker = n * n := by rw [mul_comm, hprod]
    exact Nat.mul_left_cancel hnpos (le_antisymm (h2.trans (h3.trans_eq h4)) h1)
  have hker_eq_card : Nat.card ψ.ker = n := by
    have h3 : n * Nat.card ψ.ker ≤ Nat.card ψ.range * Nat.card ψ.ker :=
      Nat.mul_le_mul_right _ hYrange_le
    have h4 : Nat.card ψ.range * Nat.card ψ.ker = n * n := by rw [mul_comm, hprod]
    have h5 : n * n ≤ n * Nat.card ψ.ker := Nat.mul_le_mul_left n hYker_le
    exact Nat.mul_left_cancel hnpos (le_antisymm (h3.trans_eq h4) h5)
  have hker_eq : Y'.map mk = ψ.ker :=
    Subgroup.eq_of_le_of_card_ge hYker (by rw [hker_eq_card, hn])
  have hpre : (Y'.map mk).comap mk = Y' := by
    rw [Subgroup.comap_map_eq, QuotientGroup.ker_mk', sup_eq_left.mpr hV'Y']
  intro m hm hmt
  have hmm_ker : mk (⟨m, hm⟩ : ↥M) ∈ ψ.ker := by
    rw [MonoidHom.mem_ker, hψmk]
    have hmem : σM (⟨m, hm⟩ : ↥M) * (⟨m, hm⟩ : ↥M)⁻¹ ∈ V' := by
      show t * m * t⁻¹ * m⁻¹ ∈ V
      have h : ⁅t, m⁆ ∈ V := hmt
      rwa [commutatorElement_def] at h
    rw [show mk (σM (⟨m, hm⟩ : ↥M)) * (mk (⟨m, hm⟩ : ↥M))⁻¹
          = mk (σM (⟨m, hm⟩ : ↥M) * (⟨m, hm⟩ : ↥M)⁻¹) by rw [← map_inv, ← map_mul]]
    exact (QuotientGroup.eq_one_iff (σM (⟨m, hm⟩ : ↥M) * (⟨m, hm⟩ : ↥M)⁻¹)).mpr hmem
  have hmm_YV : mk (⟨m, hm⟩ : ↥M) ∈ Y'.map mk := hker_eq ▸ hmm_ker
  have hmm_Y' : (⟨m, hm⟩ : ↥M) ∈ Y' := by
    have : (⟨m, hm⟩ : ↥M) ∈ (Y'.map mk).comap mk := hmm_YV
    rwa [hpre] at this
  exact hmm_Y'

theorem mem_normalizer_cent_sup_zpowers {V : Subgroup G} {t x : G} (hV : IsElemAbelian 2 V)
    (ht : t * t = 1) (htV : ∀ v ∈ V, t * v * t⁻¹ ∈ V) (hxV : ∀ v ∈ V, x * v * x⁻¹ ∈ V)
    (hxt : ⁅x, t⁆ ∈ V) : x ∈ normalizer ((centEl V t ⊔ zpowers t : Subgroup G) : Set G) := by
  set w := ⁅x, t⁆ with hwdef
  have hwV : w ∈ V := hxt
  have hxteq : x * t * x⁻¹ = w * t := by rw [hwdef]; group
  have hwt2 : (w * t) * (w * t) = 1 := by
    rw [← hxteq]
    calc (x * t * x⁻¹) * (x * t * x⁻¹) = x * (t * (x⁻¹ * x) * t) * x⁻¹ := by group
      _ = x * (t * t) * x⁻¹ := by rw [inv_mul_cancel]; group
      _ = 1 := by rw [ht]; group
  have hw2 : w * w = 1 := by
    have := hV.2 w hwV
    rwa [pow_two] at this
  have hcomm : t * w = w * t := by
    have ht_inv : t⁻¹ = t := (eq_inv_of_mul_eq_one_right ht).symm
    have hw_inv : w⁻¹ = w := (eq_inv_of_mul_eq_one_right hw2).symm
    have hu : (w * t)⁻¹ = w * t := by
      rw [inv_eq_iff_mul_eq_one]; exact hwt2
    calc t * w = (w * t)⁻¹ := by rw [mul_inv_rev, ht_inv, hw_inv]
      _ = w * t := hu
  have hwcent : w ∈ centEl V t :=
    ⟨hwV, Subgroup.mem_centralizer_singleton_iff.mpr hcomm.symm⟩
  have hcommV : ∀ a ∈ V, ∀ b ∈ V, a * b = b * a := by
    intro a ha b hb
    haveI : IsMulCommutative V := hV.1
    exact congrArg Subtype.val (mul_comm' (⟨a, ha⟩ : V) ⟨b, hb⟩)
  have hcent_map : (centEl V t).map (MulAut.conj x) ≤ centEl V t := by
    intro y hy
    rw [Subgroup.mem_map] at hy
    obtain ⟨c, hc, rfl⟩ := hy
    refine ⟨by simpa [MulAut.conj_apply] using hxV c hc.1, ?_⟩
    have hc2 : c * t = t * c := Subgroup.mem_centralizer_singleton_iff.mp hc.2
    have hconj_comm : (x * c * x⁻¹) * (x * t * x⁻¹) = (x * t * x⁻¹) * (x * c * x⁻¹) := by
      calc (x * c * x⁻¹) * (x * t * x⁻¹) = x * (c * t) * x⁻¹ := by group
        _ = x * (t * c) * x⁻¹ := by rw [hc2]
        _ = (x * t * x⁻¹) * (x * c * x⁻¹) := by group
    rw [hxteq] at hconj_comm
    have h2 : w * ((x * c * x⁻¹) * t) = w * (t * (x * c * x⁻¹)) := by
      calc w * ((x * c * x⁻¹) * t) = (w * (x * c * x⁻¹)) * t := by group
        _ = ((x * c * x⁻¹) * w) * t := by rw [hcommV w hwV (x * c * x⁻¹) (hxV c hc.1)]
        _ = (x * c * x⁻¹) * (w * t) := by group
        _ = (w * t) * (x * c * x⁻¹) := hconj_comm
        _ = w * (t * (x * c * x⁻¹)) := by group
    refine Subgroup.mem_centralizer_singleton_iff.mpr ?_
    change (x * c * x⁻¹) * t = t * (x * c * x⁻¹)
    exact mul_left_cancel h2
  have hpowers_map : (zpowers t).map (MulAut.conj x) ≤ centEl V t ⊔ zpowers t := by
    rw [MonoidHom.map_zpowers, Subgroup.zpowers_le]
    show MulAut.conj x t ∈ centEl V t ⊔ zpowers t
    rw [MulAut.conj_apply, hxteq]
    exact Subgroup.mul_mem_sup hwcent (Subgroup.mem_zpowers t)
  have hmap_le : (centEl V t ⊔ zpowers t).map (MulAut.conj x) ≤ centEl V t ⊔ zpowers t := by
    rw [Subgroup.map_sup]
    exact sup_le (hcent_map.trans le_sup_left) hpowers_map
  refine Subgroup.mem_normalizer_fintype fun y hy => ?_
  have := hmap_le (Subgroup.mem_map_of_mem (MulAut.conj x : G →* G) hy)
  simpa [MulAut.conj_apply] using this

end CFSG.OddStandard.HigherRank.YamadaG23
