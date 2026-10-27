module

public import CFSG.GroupTheory.Gorenstein.MaxOrderThompson
public import CFSG.GroupTheory.ThompsonIndexTwo
public import CFSG.GroupTheory.AutomorphismAction.AbelianTwoGroupSplitting
public import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.CardSupOfDisjointNormalizer
public import CFSG.GroupTheory.CentralizerSup
public import CFSG.GroupTheory.GL52.Basic
public import CFSG.GroupTheory.SupMulCommutative

public section

namespace CFSG.GroupTheory

open scoped Pointwise commutatorElement

variable {H : Type*} [Group H]

theorem three_dvd_orderOf_of_fixedPointFree_of_card_le_four {V : Type*} [Group V] [Finite V]
    [Nontrivial V] (φ : MulAut V) (hodd : Odd (orderOf φ))
    (hfree : ∀ v : V, v ≠ 1 → φ v ≠ v) (hcard : Nat.card V ≤ 4) :
    3 ∣ orderOf φ := by
  classical
  let C : Subgroup (MulAut V) := Subgroup.zpowers φ
  letI : MulAction C V := MulAction.compHom V C.subtype
  obtain ⟨v, hv1⟩ := exists_ne (1 : V)
  let O : Set V := MulAction.orbit C v
  have hvO : v ∈ O := MulAction.mem_orbit_self v
  have hOsub : O ⊆ {w : V | w ≠ 1} := by
    intro w hw
    rw [MulAction.mem_orbit_iff] at hw
    obtain ⟨c, rfl⟩ := hw
    simp only [Set.mem_setOf_eq]
    intro h
    have hcv : c • v = (c : MulAut V) v := rfl
    rw [hcv] at h
    exact hv1 ((c : MulAut V).injective (by rw [h, map_one]))
  have hOge2 : 2 ≤ O.ncard := by
    by_contra hlt
    have hle1 : O.ncard ≤ 1 := by omega
    have hpos : 0 < O.ncard := by
      rw [Set.ncard_pos]
      exact ⟨v, hvO⟩
    have h1 : O.ncard = 1 := by omega
    obtain ⟨a, ha⟩ := Set.ncard_eq_one.mp h1
    have hav : a = v := by
      have hv' : v ∈ ({a} : Set V) := ha ▸ hvO
      simpa [eq_comm] using hv'
    have hmem : φ v ∈ O := by
      rw [MulAction.mem_orbit_iff]
      exact ⟨⟨φ, Subgroup.mem_zpowers φ⟩, rfl⟩
    rw [ha, hav] at hmem
    exact hfree v hv1 (by simpa using hmem)
  have hOle3 : O.ncard ≤ 3 := by
    have hle : O.ncard ≤ ({w : V | w ≠ 1} : Set V).ncard :=
      Set.ncard_le_ncard hOsub (Set.toFinite _)
    have hcompl : ({w : V | w ≠ 1} : Set V) = Set.univ \ ({1} : Set V) := by
      ext w
      simp
    have hcardcompl : ({w : V | w ≠ 1} : Set V).ncard = Nat.card V - 1 := by
      rw [hcompl, Set.ncard_sdiff_singleton_of_mem (Set.mem_univ (1 : V)),
        Set.ncard_univ V]
    omega
  have hdvd : O.ncard ∣ Nat.card C := by
    rw [← MulAction.index_stabilizer C v]
    exact Subgroup.index_dvd_card _
  have hCcard : Nat.card C = orderOf φ := Nat.card_zpowers φ
  have hoddC : Odd (Nat.card C) := hCcard ▸ hodd
  have hoddO : Odd O.ncard := Odd.of_dvd_nat hoddC hdvd
  have hO3 : O.ncard = 3 := by
    obtain ⟨k, hk⟩ := hoddO
    omega
  rw [hCcard] at hdvd
  rwa [hO3] at hdvd

theorem relIndex_center_le_two_of_maxCardAbelian_not_le [Finite H]
    {S Q B : Subgroup H}
    (hQleS : Q ≤ S) (hQrel : Q.relIndex S = 2)
    (hB : B ∈ ambientMaxCardAbelianFamily S)
    {b s : H} (hbB : b ∈ B) (hbQ : b ∉ Q) (hsS : s ∈ S) (hsQ : s ∉ Q) :
    ((Subgroup.center ↥Q).map Q.subtype ⊓ Subgroup.centralizer ({s} : Set H)).relIndex
      ((Subgroup.center ↥Q).map Q.subtype) ≤ 2 := by
  classical
  let Z : Subgroup H := (Subgroup.center ↥Q).map Q.subtype
  let C : Subgroup H := Z ⊓ Subgroup.centralizer ({s} : Set H)
  have hZleQ : Z ≤ Q := Subgroup.map_subtype_le _
  have hZcent : Z ≤ Subgroup.centralizer (Q : Set H) := by
    rw [show Z = Q ⊓ Subgroup.centralizer (Q : Set H) from
      CFSG.center_map_subtype_eq_inf_centralizer Q]
    exact inf_le_right
  have hZab : IsMulCommutative ↥Z := by
    refine IsMulCommutative.of_comm fun x y => ?_
    apply Subtype.ext
    exact Subgroup.mem_centralizer_iff.mp (hZcent y.2) x (hZleQ x.2)
  have hbS : b ∈ S := hB.1 hbB
  have hbsQ : b⁻¹ * s ∈ Q :=
    CFSG.ThompsonIndexTwo.inv_mul_mem_of_not_mem hQrel hbS hsS hbQ hsQ
  let q : H := (b⁻¹ * s)⁻¹
  have hqQ : q ∈ Q := Q.inv_mem hbsQ
  have hbq : b = s * q := by
    dsimp [q]
    group
  let Cb : Subgroup H := Z ⊓ Subgroup.centralizer ({b} : Set H)
  have hCbab : IsMulCommutative ↥Cb := by
    refine IsMulCommutative.of_comm fun x y => ?_
    apply Subtype.ext
    simpa using congrArg Subtype.val (hZab.is_comm.comm
      ⟨x, (inf_le_left : Cb ≤ Z) x.2⟩ ⟨y, (inf_le_left : Cb ≤ Z) y.2⟩)
  have hBCcomm : ∀ x ∈ B, ∀ c ∈ Cb, x * c = c * x := by
    intro x hx c hc
    obtain ⟨hcZ, hcCb⟩ := Subgroup.mem_inf.mp hc
    have hcQ : c ∈ Q := hZleQ hcZ
    have hcQcent := hZcent hcZ
    have hcq : c * q = q * c :=
      (Subgroup.mem_centralizer_iff.mp hcQcent q hqQ).symm
    have hcb : c * b = b * c := Subgroup.mem_centralizer_singleton_iff.mp hcCb
    have hcs : c * s = s * c := by
      have h1 : (c * s) * q = s * (c * q) := by
        calc (c * s) * q = c * b := by rw [hbq]; group
          _ = b * c := hcb
          _ = (s * q) * c := by rw [hbq]
          _ = s * (c * q) := by rw [hcq]; group
      have h2 : (c * s) * q = (s * c) * q := by
        calc (c * s) * q = s * (c * q) := h1
          _ = (s * c) * q := by group
      exact mul_right_cancel h2
    by_cases hxQ : x ∈ Q
    · exact Subgroup.mem_centralizer_iff.mp hcQcent x hxQ
    · have hxsQ : x⁻¹ * s ∈ Q :=
        CFSG.ThompsonIndexTwo.inv_mul_mem_of_not_mem hQrel (hB.1 hx) hsS hxQ hsQ
      let qx : H := (x⁻¹ * s)⁻¹
      have hqxQ : qx ∈ Q := Q.inv_mem hxsQ
      have hxq : x = s * qx := by
        dsimp [qx]
        group
      have hcqx : c * qx = qx * c :=
        (Subgroup.mem_centralizer_iff.mp hcQcent qx hqxQ).symm
      calc x * c = (s * qx) * c := by rw [hxq]
        _ = s * (qx * c) := by group
        _ = s * (c * qx) := by rw [hcqx]
        _ = (s * c) * qx := by group
        _ = (c * s) * qx := by rw [hcs]
        _ = c * (s * qx) := by group
        _ = c * x := by rw [← hxq]
  have hDS : B ⊔ Cb ≤ S := by
    refine sup_le hB.1 ?_
    exact (inf_le_left.trans hZleQ).trans hQleS
  have hDab : IsMulCommutative ↥(B ⊔ Cb : Subgroup H) :=
    isMulCommutative_sup_of_elementwise_commute hBCcomm hB.2.1 hCbab
  have hDcard : Nat.card ↥(B ⊔ Cb) ≤ Nat.card B := hB.2.2 _ hDS hDab
  have hD_eq : B ⊔ Cb = B :=
    (Subgroup.eq_of_le_of_card_ge le_sup_left hDcard).symm
  have hCb_le_B : Cb ≤ B := hD_eq ▸ le_sup_right
  have hCb_eq : Cb = B ⊓ Z := by
    refine le_antisymm (le_inf hCb_le_B inf_le_left) ?_
    intro x hx
    obtain ⟨hxB, hxZ⟩ := Subgroup.mem_inf.mp hx
    refine Subgroup.mem_inf.mpr ⟨hxZ, ?_⟩
    exact Subgroup.mem_centralizer_singleton_iff.mpr
      (congrArg Subtype.val (hB.2.1.is_comm.comm ⟨x, hxB⟩ ⟨b, hbB⟩))
  have hcent_bs : ∀ c : H, c ∈ Z → (c * b = b * c ↔ c * s = s * c) := by
    intro c hcZ
    have hcq : c * q = q * c :=
      (Subgroup.mem_centralizer_iff.mp (hZcent hcZ) q hqQ).symm
    constructor
    · intro hcb
      have h1 : (c * s) * q = s * (c * q) := by
        calc (c * s) * q = c * b := by rw [hbq]; group
          _ = b * c := hcb
          _ = (s * q) * c := by rw [hbq]
          _ = s * (c * q) := by rw [hcq]; group
      have h2 : (c * s) * q = (s * c) * q := by
        calc (c * s) * q = s * (c * q) := h1
          _ = (s * c) * q := by group
      exact mul_right_cancel h2
    · intro hcs
      calc c * b = c * (s * q) := by rw [hbq]
        _ = (c * s) * q := by group
        _ = (s * c) * q := by rw [hcs]
        _ = s * (c * q) := by group
        _ = s * (q * c) := by rw [hcq]
        _ = (s * q) * c := by group
        _ = b * c := by rw [← hbq]
  have hCb_eq_C : Cb = C := by
    refine le_antisymm ?_ ?_
    · intro x hx
      obtain ⟨hxZ, hxCb⟩ := Subgroup.mem_inf.mp hx
      refine Subgroup.mem_inf.mpr ⟨hxZ, ?_⟩
      exact Subgroup.mem_centralizer_singleton_iff.mpr
        ((hcent_bs x hxZ).mp (Subgroup.mem_centralizer_singleton_iff.mp hxCb))
    · intro x hx
      obtain ⟨hxZ, hxC⟩ := Subgroup.mem_inf.mp hx
      refine Subgroup.mem_inf.mpr ⟨hxZ, ?_⟩
      exact Subgroup.mem_centralizer_singleton_iff.mpr
        ((hcent_bs x hxZ).mpr (Subgroup.mem_centralizer_singleton_iff.mp hxC))
  have hQrelB_le : Q.relIndex B ≤ Q.relIndex S :=
    Subgroup.relIndex_le_of_le_right hB.1 (by rw [hQrel]; norm_num)
  have hQrelB_ne0 : Q.relIndex B ≠ 0 := by
    intro h0
    exact (by rw [hQrel]; norm_num : Q.relIndex S ≠ 0)
      (Subgroup.relIndex_eq_zero_of_le_right hB.1 h0)
  have hQrelB_ne1 : Q.relIndex B ≠ 1 := by
    intro h1
    exact hbQ (Subgroup.relIndex_eq_one.mp h1 hbB)
  have hQrelB : Q.relIndex B = 2 := by omega
  have hBrel : (B ⊓ Q).relIndex B = 2 := by
    rw [Subgroup.inf_relIndex_left]
    exact hQrelB
  have hBcard : Nat.card B = 2 * Nat.card ↥(B ⊓ Q) := by
    have h := Subgroup.relIndex_mul_card (H := B ⊓ Q) (K := B)
    rw [inf_eq_left.mpr (inf_le_left : B ⊓ Q ≤ B), hBrel] at h
    exact h.symm
  let T : Subgroup H := (B ⊓ Q) ⊔ Z
  have hBQ_le_S : B ⊓ Q ≤ S := inf_le_left.trans hB.1
  have hTleS : T ≤ S := sup_le hBQ_le_S (hZleQ.trans hQleS)
  have hBQab : IsMulCommutative ↥(B ⊓ Q : Subgroup H) := by
    refine IsMulCommutative.of_comm fun x y => ?_
    apply Subtype.ext
    simpa using congrArg Subtype.val (hB.2.1.is_comm.comm
      ⟨x, (inf_le_left : B ⊓ Q ≤ B) x.2⟩ ⟨y, (inf_le_left : B ⊓ Q ≤ B) y.2⟩)

  have hTcomm : ∀ x ∈ B ⊓ Q, ∀ y ∈ Z, x * y = y * x := by
    intro x hx y hy
    exact Subgroup.mem_centralizer_iff.mp (hZcent hy) x ((inf_le_right : B ⊓ Q ≤ Q) hx)
  have hTab : IsMulCommutative ↥T :=
    isMulCommutative_sup_of_elementwise_commute hTcomm hBQab hZab
  have hTcard_le : Nat.card T ≤ Nat.card B := hB.2.2 T hTleS hTab
  have hTcard : (B ⊓ Q).relIndex T * Nat.card ↥(B ⊓ Q) = Nat.card T := by
    have h := Subgroup.relIndex_mul_card (H := B ⊓ Q) (K := T)
    rwa [inf_eq_left.mpr (le_sup_left : B ⊓ Q ≤ T)] at h
  have hrelT_le : (B ⊓ Q).relIndex T ≤ 2 := by
    have hpos : 0 < Nat.card ↥(B ⊓ Q) := Nat.card_pos
    refine Nat.le_of_mul_le_mul_right ?_ hpos
    rw [hTcard, ← hBcard]
    exact hTcard_le
  have hTrel : (B ⊓ Q).relIndex T = (B ⊓ Z).relIndex Z := by
    let K : Subgroup ↥T := (B ⊓ Q).subgroupOf T
    let L : Subgroup ↥T := Z.subgroupOf T
    letI : IsMulCommutative ↥T := hTab
    haveI : K.Normal := inferInstance
    have hsup : L ⊔ K = ⊤ := by
      dsimp [L, K]
      rw [← Subgroup.subgroupOf_sup (le_sup_right : Z ≤ T) (le_sup_left : B ⊓ Q ≤ T)]
      rw [show Z ⊔ (B ⊓ Q) = T from by rw [sup_comm]]
      exact Subgroup.subgroupOf_self T
    have h1 : K.relIndex ⊤ = K.relIndex L := by
      have h := Subgroup.relIndex_sup_right (H := L) (K := K)
      rw [hsup] at h
      exact h
    have h2 : K.relIndex L = (B ⊓ Q).relIndex Z :=
      Subgroup.relIndex_subgroupOf (le_sup_right : Z ≤ T)
    calc (B ⊓ Q).relIndex T = K.index := rfl
      _ = K.relIndex ⊤ := (Subgroup.relIndex_top_right K).symm
      _ = K.relIndex L := h1
      _ = (B ⊓ Q).relIndex Z := h2
      _ = (B ⊓ Z).relIndex Z := by
        rw [← Subgroup.inf_relIndex_right (H := B ⊓ Q) (K := Z), inf_assoc,
          inf_eq_right.mpr hZleQ]
  have hrelBZ : (B ⊓ Z).relIndex Z ≤ 2 := by
    rw [← hTrel]
    exact hrelT_le
  have hCrel : C.relIndex Z ≤ 2 := by
    rw [show C = B ⊓ Z by rw [← hCb_eq_C, hCb_eq]]
    exact hrelBZ
  exact hCrel

theorem mem_centralizer_of_relIndex_center_le_two [Finite H] {A Z : Subgroup H}
    (hAodd : Odd (Nat.card A)) (h3A : ¬ 3 ∣ Nat.card A)
    (hZ2 : IsPGroup 2 Z) (hZab : IsMulCommutative ↥Z)
    (hAZ : A ≤ Subgroup.normalizer (Z : Set H))
    {s : H} (hsN : s ∈ Subgroup.normalizer (A : Set H))
    (hBinv : ∀ x ∈ ⁅A, Subgroup.zpowers s⁆, s * x * s⁻¹ = x⁻¹)
    (hCindex : (Z ⊓ Subgroup.centralizer ({s} : Set H)).relIndex Z ≤ 2)
    {a : H} (haB : a ∈ ⁅A, Subgroup.zpowers s⁆) :
    a ∈ Subgroup.centralizer (Z : Set H) := by
  classical
  have hAsN : Subgroup.zpowers s ≤ Subgroup.normalizer (A : Set H) :=
    Subgroup.zpowers_le.mpr hsN
  have hBcom_le_A : ⁅A, Subgroup.zpowers s⁆ ≤ A :=
    Subgroup.le_normalizer_iff_commutator_le_left.mp hAsN
  have haA : a ∈ A := hBcom_le_A haB
  have haZ : a ∈ Subgroup.normalizer (Z : Set H) := hAZ haA
  have hsa : s * a * s⁻¹ = a⁻¹ := hBinv a haB
  have hsa_inv : s * a⁻¹ * s⁻¹ = a := by
    have := congrArg Inv.inv hsa
    simpa [mul_inv_rev, mul_assoc] using this
  let s' : H := a⁻¹ * s * a
  have ha2_eq : a ^ 2 = s * (s')⁻¹ := by
    dsimp [s']
    rw [pow_two]
    calc a * a = (s * a⁻¹ * s⁻¹) * a := by rw [hsa_inv]
      _ = s * (a⁻¹ * s * a)⁻¹ := by
        rw [mul_inv_rev, mul_inv_rev]
        simp [mul_assoc]
  let Cs : Subgroup H := Z ⊓ Subgroup.centralizer ({s} : Set H)
  let Cs' : Subgroup H := Z ⊓ Subgroup.centralizer ({s'} : Set H)
  let Ca : Subgroup H := Z ⊓ Subgroup.centralizer ({a} : Set H)
  let α : MulAut H := MulAut.conj a
  have hZmap : Z.map (α : H →* H) = Z := by
    have := Subgroup.mem_normalizer_iff_map_conj_eq.mp haZ
    simpa [α] using this
  have hCs'map : (Subgroup.centralizer ({s'} : Set H)).map (α : H →* H) =
      Subgroup.centralizer ({s} : Set H) := by
    have h := CFSG.GroupTheory.GL52.centralizer_map_conj a (Subgroup.zpowers s')
    rw [MonoidHom.map_zpowers] at h
    have hs' : (MulEquiv.toMonoidHom (MulAut.conj a)) s' = s := by
      dsimp [s']
      group
    rw [hs'] at h
    rw [CFSG.centralizer_zpowers_eq_centralizer_singleton s,
      CFSG.centralizer_zpowers_eq_centralizer_singleton s'] at h
    simpa [α] using h.symm
  have hCs' : Cs'.relIndex Z ≤ 2 := by
    have hmap := Subgroup.relIndex_map_map_of_injective (H := Cs') (K := Z)
      (f := (α : H →* H)) α.injective
    rw [hZmap] at hmap
    have hmaps : Cs'.map (α : H →* H) = Cs := by
      dsimp [Cs, Cs']
      rw [Subgroup.map_inf_eq _ _ _ α.injective, hZmap, hCs'map]
    rw [hmaps] at hmap
    rw [← hmap]
    exact hCindex
  have hCs_inf_le : (Cs ⊓ Cs').relIndex Z ≤ 4 := by
    have h1 : (Cs ⊓ Cs').relIndex Z ≤ Cs.relIndex Z * Cs'.relIndex Z :=
      Subgroup.relIndex_inf_le
    have h2 : Cs.relIndex Z * Cs'.relIndex Z ≤ 2 * 2 :=
      Nat.mul_le_mul hCindex hCs'
    calc (Cs ⊓ Cs').relIndex Z ≤ Cs.relIndex Z * Cs'.relIndex Z := h1
      _ ≤ 2 * 2 := h2
      _ = 4 := by norm_num
  have hCa2_eq : (Z ⊓ Subgroup.centralizer ({a ^ 2} : Set H)) = Ca := by
    have hzp : Subgroup.zpowers a = Subgroup.zpowers (a ^ 2) := by
      have hoddA : Odd (orderOf a) :=
        Odd.of_dvd_nat hAodd (Subgroup.orderOf_dvd_natCard A haA)
      have hcop : Nat.Coprime 2 (orderOf a) := (Nat.coprime_two_right.mpr hoddA).symm
      obtain ⟨m, hm⟩ := exists_pow_eq_self_of_coprime (x := a) (n := 2) hcop
      apply le_antisymm
      · rw [Subgroup.zpowers_le]
        have hmem : (a ^ 2) ^ m ∈ Subgroup.zpowers (a ^ 2) :=
          Subgroup.pow_mem (Subgroup.zpowers (a ^ 2)) (Subgroup.mem_zpowers (a ^ 2)) m
        rwa [hm] at hmem
      · exact Subgroup.zpowers_le.mpr (Subgroup.pow_mem (Subgroup.zpowers a)
          (Subgroup.mem_zpowers a) 2)
    dsimp [Ca]
    rw [← CFSG.centralizer_zpowers_eq_centralizer_singleton a,
      ← CFSG.centralizer_zpowers_eq_centralizer_singleton (a ^ 2), hzp]
  have hle_Ca2 : Cs ⊓ Cs' ≤ Z ⊓ Subgroup.centralizer ({a ^ 2} : Set H) := by
    intro z hz
    obtain ⟨hzCs, hzCs'⟩ := Subgroup.mem_inf.mp hz
    obtain ⟨hzZ, hzC⟩ := Subgroup.mem_inf.mp hzCs
    obtain ⟨-, hzC'⟩ := Subgroup.mem_inf.mp hzCs'
    refine Subgroup.mem_inf.mpr ⟨hzZ, ?_⟩
    rw [Subgroup.mem_centralizer_singleton_iff] at hzC hzC' ⊢
    have hcomm : Commute z (s * (s')⁻¹) :=
      ((commute_iff_eq z s).mpr hzC).mul_right
        (((commute_iff_eq z s').mpr hzC').inv_right)
    rw [ha2_eq]
    exact hcomm.eq
  have hCs_inf_ne0 : (Cs ⊓ Cs').relIndex Z ≠ 0 := by
    have hCs_ne0 : Cs.relIndex Z ≠ 0 := by
      have hpos : 0 < Cs.relIndex Z :=
        Nat.pos_of_dvd_of_pos (Subgroup.relIndex_dvd_card Cs Z) Nat.card_pos
      omega
    have hCs'_ne0 : Cs'.relIndex Z ≠ 0 := by
      have hpos : 0 < Cs'.relIndex Z :=
        Nat.pos_of_dvd_of_pos (Subgroup.relIndex_dvd_card Cs' Z) Nat.card_pos
      omega
    exact Subgroup.relIndex_inf_ne_zero hCs_ne0 hCs'_ne0
  have hCa2 : (Z ⊓ Subgroup.centralizer ({a ^ 2} : Set H)).relIndex Z ≤ 4 := by
    have hle := Subgroup.relIndex_le_of_le_left hle_Ca2 hCs_inf_ne0
    exact hle.trans hCs_inf_le
  have hCa : Ca.relIndex Z ≤ 4 := by
    rw [← hCa2_eq]
    exact hCa2
  have hzpow : Subgroup.zpowers a ≤ Subgroup.normalizer (Z : Set H) :=
    Subgroup.zpowers_le.mpr haZ
  have hAodd' : Odd (Nat.card ↥(Subgroup.zpowers a)) := by
    rw [Nat.card_zpowers]
    exact Odd.of_dvd_nat hAodd (Subgroup.orderOf_dvd_natCard A haA)
  obtain ⟨hsup, hdisj, -⟩ :=
    CFSG.GroupTheory.AutomorphismAction.abelian_twoGroup_splitting Z
      (Subgroup.zpowers a) hZ2 hAodd' hzpow hZab
  let V : Subgroup H := ⁅Z, Subgroup.zpowers a⁆
  have hVleZ : V ≤ Z := Subgroup.le_normalizer_iff_commutator_le_left.mp hzpow
  have hCa_eq : Ca = Z ⊓ Subgroup.centralizer (Subgroup.zpowers a : Set H) := by
    dsimp [Ca]
    rw [CFSG.centralizer_zpowers_eq_centralizer_singleton a]
  have hdisj_a : V ⊓ Ca = ⊥ := by
    rw [hCa_eq, eq_bot_iff]
    intro z hz
    obtain ⟨hzV, hzZC⟩ := Subgroup.mem_inf.mp hz
    obtain ⟨hzZ, hzC⟩ := Subgroup.mem_inf.mp hzZC
    have hzbot : Subgroup.zpowers z ≤ ⊥ :=
      hdisj (Subgroup.zpowers_le.mpr hzV)
        (Subgroup.zpowers_le.mpr (Subgroup.mem_inf.mpr ⟨hzZ, hzC⟩))
    exact hzbot (Subgroup.mem_zpowers z)
  have hsup_a : V ⊔ Ca = Z := by
    simpa [V, Ca, CFSG.centralizer_zpowers_eq_centralizer_singleton a] using hsup
  by_cases hVbot : V = ⊥
  · rw [Subgroup.mem_centralizer_iff]
    intro z hz
    have hCa_eq_Z : Ca = Z := by
      rw [← hsup_a, hVbot, bot_sup_eq]
    have hZle : Z ≤ Subgroup.centralizer (Subgroup.zpowers a) := by
      rw [← hCa_eq_Z, hCa_eq]
      exact inf_le_right
    exact (Subgroup.mem_centralizer_iff.mp (hZle hz) a (Subgroup.mem_zpowers a)).symm
  · exfalso
    have hVne : V ≠ ⊥ := hVbot
    haveI : Nontrivial V := (Subgroup.nontrivial_iff_ne_bot V).mpr hVne
    have haNV : a ∈ Subgroup.normalizer (V : Set H) :=
      Subgroup.normalizer_commutator_ge_right Z (Subgroup.zpowers a)
        (Subgroup.mem_zpowers a)
    let φ : MulAut V := Subgroup.normalizerMonoidHom V ⟨a, haNV⟩
    have hφdvd : orderOf φ ∣ orderOf a := by
      let ψ : Subgroup.zpowers a →* MulAut V :=
        (Subgroup.normalizerMonoidHom V).comp
          (Subgroup.inclusion (Subgroup.zpowers_le.mpr haNV))
      have hψa : ψ ⟨a, Subgroup.mem_zpowers a⟩ = φ := rfl
      have h := orderOf_map_dvd ψ ⟨a, Subgroup.mem_zpowers a⟩
      rwa [hψa, Subgroup.orderOf_mk] at h
    have haodd : Odd (orderOf a) :=
      Odd.of_dvd_nat hAodd (Subgroup.orderOf_dvd_natCard A haA)
    have hφodd : Odd (orderOf φ) := Odd.of_dvd_nat haodd hφdvd
    have hfree : ∀ v : V, v ≠ 1 → φ v ≠ v := by
      intro v hv hfix
      apply hv
      have hva : (v : H) ∈ Subgroup.centralizer ({a} : Set H) := by
        rw [Subgroup.mem_centralizer_singleton_iff]
        have hcoe := Subgroup.normalizerMonoidHom_apply_apply_coe V ⟨a, haNV⟩ v
        have hvfix : a * (v : H) * a⁻¹ = (v : H) := by
          rw [← hcoe, hfix]
        calc (v : H) * a = (a * (v : H) * a⁻¹) * a := by rw [hvfix]
          _ = a * (v : H) := by group
      have hmem : (v : H) ∈ V ⊓ (Z ⊓ Subgroup.centralizer ({a} : Set H)) :=
        Subgroup.mem_inf.mpr ⟨v.2, Subgroup.mem_inf.mpr ⟨hVleZ v.2, hva⟩⟩
      have hdisj' : V ⊓ (Z ⊓ Subgroup.centralizer ({a} : Set H)) = ⊥ := by
        rw [show Z ⊓ Subgroup.centralizer ({a} : Set H) = Ca by
          rw [hCa_eq, CFSG.centralizer_zpowers_eq_centralizer_singleton a]]
        exact hdisj_a
      rw [hdisj'] at hmem
      exact Subtype.ext (Subgroup.mem_bot.mp hmem)
    have hcardV : Nat.card V ≤ 4 := by
      have hVsup : V ⊔ Ca = Z := hsup_a
      have hVinf : V ⊓ Ca = ⊥ := hdisj_a
      letI : IsMulCommutative ↥Z := hZab
      let Y : Subgroup ↥Z := Ca.subgroupOf Z
      let A : Subgroup ↥Z := V.subgroupOf Z
      haveI : Y.Normal := inferInstance
      have hinfY : A ⊓ Y = ⊥ := by
        ext x
        constructor
        · intro hx
          obtain ⟨hxA, hxY⟩ := Subgroup.mem_inf.mp hx
          have hxV : (x : H) ∈ V := Subgroup.mem_subgroupOf.mp hxA
          have hxCa : (x : H) ∈ Ca := Subgroup.mem_subgroupOf.mp hxY
          have hxbot : (x : H) ∈ V ⊓ Ca := Subgroup.mem_inf.mpr ⟨hxV, hxCa⟩
          rw [hVinf] at hxbot
          rw [Subgroup.mem_bot]
          exact Subtype.ext (Subgroup.mem_bot.mp hxbot)
        · intro hx
          rw [Subgroup.mem_bot] at hx
          rw [hx]
          exact Subgroup.one_mem _
      have hsupY : Y ⊔ A = ⊤ := by
        dsimp [Y, A]
        rw [← Subgroup.subgroupOf_sup (inf_le_left : Ca ≤ Z) hVleZ]
        rw [show Ca ⊔ V = Z from by rw [sup_comm]; exact hVsup]
        exact Subgroup.subgroupOf_self Z
      letI : CommGroup ↥Z := IsMulCommutative.instCommGroup
      have hdisjYA : Disjoint Y A := by
        rw [disjoint_iff]
        rwa [inf_comm]
      have hnormalYA : A ≤ Subgroup.normalizer (Y : Set ↥Z) := by
        rw [CommGroup.normalizer_eq_top]
        exact le_top
      have hcardT : Nat.card ↥(Y ⊔ A) = Nat.card Y * Nat.card A :=
        CFSG.GorensteinWalter.card_sup_eq_mul_of_disjoint_of_le_normalizer
          Y A hnormalYA hdisjYA
      have hYcard : Nat.card Y = Nat.card Ca :=
        Nat.card_congr (Subgroup.subgroupOfEquivOfLe (inf_le_left : Ca ≤ Z)).toEquiv
      have hAcard : Nat.card A = Nat.card V :=
        Nat.card_congr (Subgroup.subgroupOfEquivOfLe hVleZ).toEquiv
      rw [hsupY, Subgroup.card_top, hYcard, hAcard] at hcardT
      have hrelZ : Ca.relIndex Z * Nat.card Ca = Nat.card Z := by
        have h := Subgroup.relIndex_mul_card (H := Ca) (K := Z)
        rwa [inf_eq_left.mpr (inf_le_left : Ca ≤ Z)] at h
      have hVcard : Nat.card V = Ca.relIndex Z := by
        refine Nat.eq_of_mul_eq_mul_right (Nat.card_pos (α := ↥Ca)) ?_
        calc Nat.card V * Nat.card Ca = Nat.card Ca * Nat.card V := by rw [mul_comm]
          _ = Nat.card Z := hcardT.symm
          _ = Ca.relIndex Z * Nat.card Ca := hrelZ.symm
      rw [hVcard]
      exact hCa
    have h3φ := three_dvd_orderOf_of_fixedPointFree_of_card_le_four φ hφodd hfree hcardV
    have h3a : 3 ∣ orderOf a := h3φ.trans hφdvd
    exact h3A (h3a.trans (Subgroup.orderOf_dvd_natCard A haA))

theorem thompsonSubgroup_eq_of_commutator_center_ne [Finite H] {A S Q : Subgroup H}
    (hAodd : Odd (Nat.card A)) (h3A : ¬ 3 ∣ Nat.card A)
    (hS2 : IsPGroup 2 S) (hQleS : Q ≤ S) (hQrel : Q.relIndex S = 2)
    (hAQ : A ≤ Subgroup.normalizer (Q : Set H))
    {s : H} (hsS : s ∈ S) (hsQ : s ∉ Q)
    (hsN : s ∈ Subgroup.normalizer (A : Set H))
    (hBinv : ∀ x ∈ ⁅A, Subgroup.zpowers s⁆, s * x * s⁻¹ = x⁻¹)
    (hZ : ⁅(Subgroup.center ↥Q).map Q.subtype, ⁅A, Subgroup.zpowers s⁆⁆ ≠ ⊥) :
    CFSG.Open.thompsonSubgroup S = CFSG.Open.thompsonSubgroup Q := by
  classical
  let Z : Subgroup H := (Subgroup.center ↥Q).map Q.subtype
  let Bcom : Subgroup H := ⁅A, Subgroup.zpowers s⁆
  have hZleQ : Z ≤ Q := Subgroup.map_subtype_le _
  have hZcent : Z ≤ Subgroup.centralizer (Q : Set H) := by
    rw [show Z = Q ⊓ Subgroup.centralizer (Q : Set H) from
      CFSG.center_map_subtype_eq_inf_centralizer Q]
    exact inf_le_right
  have hZab : IsMulCommutative ↥Z := by
    refine IsMulCommutative.of_comm fun x y => ?_
    apply Subtype.ext
    exact Subgroup.mem_centralizer_iff.mp (hZcent y.2) x (hZleQ x.2)
  have hZ2 : IsPGroup 2 Z := hS2.to_le (hZleQ.trans hQleS)
  have hAZ : A ≤ Subgroup.normalizer (Z : Set H) :=
    hAQ.trans (CFSG.normalizer_le_normalizer_image_of_characteristic Q
      (Subgroup.center ↥Q))
  have hfam_le : ∀ B ∈ ambientMaxCardAbelianFamily S, B ≤ Q := by
    intro B hB
    by_contra hBQ
    rw [SetLike.le_def] at hBQ
    push_neg at hBQ
    obtain ⟨b, hbB, hbQ⟩ := hBQ
    have hCindex :=
      relIndex_center_le_two_of_maxCardAbelian_not_le hQleS hQrel hB hbB hbQ hsS hsQ
    have hBcent : Bcom ≤ Subgroup.centralizer (Z : Set H) := by
      intro a ha
      exact mem_centralizer_of_relIndex_center_le_two (A := A) (Z := Z)
        hAodd h3A hZ2 hZab hAZ hsN hBinv hCindex ha
    have hbot : ⁅Z, Bcom⁆ = ⊥ := by
      rw [Subgroup.commutator_comm, Subgroup.commutator_eq_bot_iff_le_centralizer]
      exact hBcent
    exact hZ hbot
  have hfamilies : ambientMaxCardAbelianFamily S = ambientMaxCardAbelianFamily Q := by
    ext B
    constructor
    · intro hB
      obtain ⟨hBS, hBc, hBmax⟩ := hB
      exact ⟨hfam_le B ⟨hBS, hBc, hBmax⟩, hBc,
        fun D hDQ hDc => hBmax D (hDQ.trans hQleS) hDc⟩
    · intro hB
      obtain ⟨hBQ, hBc, hBmax⟩ := hB
      obtain ⟨A₀, hA₀mem⟩ := CFSG.maxOrderAbelianFamily_nonempty (G := ↥S)
      have hA₀max : IsMaxCardAbelian A₀ :=
        CFSG.isMaxCardAbelian_iff_mem_maxOrderAbelianFamily.mpr hA₀mem
      have hCfam : A₀.map S.subtype ∈ ambientMaxCardAbelianFamily S :=
        CFSG.map_subtype_mem_ambientMaxCardAbelianFamily hA₀max
      refine ⟨hBQ.trans hQleS, hBc, ?_⟩
      intro D hDS hDc
      exact (hCfam.2.2 D hDS hDc).trans (hBmax (A₀.map S.subtype)
        (hfam_le (A₀.map S.subtype) hCfam) hCfam.2.1)
  have hJ : ambientMaxCardThompson S = ambientMaxCardThompson Q :=
    congrArg sSup hfamilies
  simpa [CFSG.Open.thompsonSubgroup, ambientMaxCardThompson] using hJ

theorem thompsonSubgroup_normal_of_commutator_center_ne [Finite H] {A S Q : Subgroup H}
    (hAodd : Odd (Nat.card A)) (h3A : ¬ 3 ∣ Nat.card A)
    (hS2 : IsPGroup 2 S) (hQleS : Q ≤ S) (hQrel : Q.relIndex S = 2)
    (hAQ : A ≤ Subgroup.normalizer (Q : Set H))
    {s : H} (hsS : s ∈ S) (hsQ : s ∉ Q)
    (hsN : s ∈ Subgroup.normalizer (A : Set H))
    (hBinv : ∀ x ∈ ⁅A, Subgroup.zpowers s⁆, s * x * s⁻¹ = x⁻¹)
    (hZ : ⁅(Subgroup.center ↥Q).map Q.subtype, ⁅A, Subgroup.zpowers s⁆⁆ ≠ ⊥)
    {X : Subgroup H} (hSX : S ≤ X) (hXQ : X ≤ Subgroup.normalizer (Q : Set H)) :
    ((CFSG.Open.thompsonSubgroup S).subgroupOf X).Normal := by
  rw [thompsonSubgroup_eq_of_commutator_center_ne hAodd h3A hS2 hQleS hQrel hAQ
    hsS hsQ hsN hBinv hZ]
  have hJQleX : CFSG.Open.thompsonSubgroup Q ≤ X :=
    (CFSG.Open.thompsonSubgroup_le_self Q).trans (hQleS.trans hSX)
  have hXN : X ≤ Subgroup.normalizer (CFSG.Open.thompsonSubgroup Q : Set H) :=
    hXQ.trans (CFSG.Open.normalizer_le_normalizer_thompsonSubgroup Q)
  exact (Subgroup.normal_subgroupOf_iff_le_normalizer hJQleX).mpr hXN

end CFSG.GroupTheory

end
