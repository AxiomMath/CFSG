module

public import CFSG.ClassicalInvolution.Q3.TL3F1Loc
public import CFSG.ClassicalInvolution.Q3.TL3EndF1P
public import CFSG.ClassicalInvolution.Q3.TL3EndGold

public section

set_option linter.unusedSectionVars false

namespace CFSG.ClassicalInvolution.Q3

open CFSG CFSG.Open CFSG.ClassicalInvolution CFSG.ClassicalInvolution.Generic
  CFSG.ClassicalInvolution.Asc77 CFSG.ClassicalInvolution.Uniform
  CFSG.ClassicalInvolution.Disconnected CFSG.ClassicalInvolution.Disconnected.AschTight

variable {G : Type} [Group G] [Finite G] {K : Subgroup G} {z : G} {S : Sylow 2 G}
  {W L : Subgroup G} {t : G} {V : Subgroup G}

namespace TightSylowDataT

variable (hd : TightSylowDataT K z S W L t V)
include hd

theorem false_of_outer {s : G} (hsS : s ∈ (S : Subgroup G)) (hs2 : s * s = 1)
    (hst : s * t * s⁻¹ = t * z)
    (hno : ¬ ∃ w ∈ (S : Subgroup G) ⊓ K, orderOf w = 4 ∧ w * s = s * w) : False := by
  have hd0 := hd.toTightSylowData
  have hΩ := hd.tight.hypGen
  have hI := hd.tight.isUniqueInvolution
  have hcomm := hd0.comm_of_mem
  have htW : t ∈ W := hd.mem_W
  have hzW : z ∈ W := hd.mem_W_z
  have hsz : s * z = z * s := Subgroup.mem_centralizer_singleton_iff.mp (hd.hSz hsS)
  have hsinv : s⁻¹ = s := inv_eq_of_mul_eq_one_left hs2
  have hsK : s ∈ Subgroup.normalizer (K : Set G) := hd0.hSN hsS
  have hsW : s ∈ Subgroup.normalizer (W : Set G) := hd.le_normalizer_W hsS
  set R : Subgroup G := (S : Subgroup G) ⊓ K with hRdef
  have hRR : R ∈ RSet (CoreAssembly.conjClass K) := hd0.inf_mem_rSet
  obtain ⟨e⟩ := hd.exists_q8_of_mem_RSet hRR
  have hzR : z ∈ R := hd0.mem_inf
  have hzs : ((e.symm (QuaternionGroup.a 2) : ↥R) : G) = z := by
    rcases TF1.Q8Sub.eq_of_mul_self_eq_one e hzR hI.sq with h | h
    · exact absurd h hI.ne_one
    · exact h.symm
  have hconjR : ∀ c ∈ (S : Subgroup G), ∀ y ∈ R, c * y * c⁻¹ ∈ R := by
    intro c hc y hy
    exact ⟨(S : Subgroup G).mul_mem ((S : Subgroup G).mul_mem hc hy.1) ((S : Subgroup G).inv_mem hc),
      (Subgroup.mem_normalizer_iff.mp (hd0.hSN hc) y).mp hy.2⟩
  have hord : ∀ y ∈ R, y * y = z → orderOf y = 4 := fun y hy h =>
    (TF1.Q8Sub.orderOf_eq_four_iff e hy).mpr (h.trans hzs.symm)
  have hcommOf : ∀ y : G, s * y * s⁻¹ = y → y * s = s * y := by
    intro y h
    calc y * s = s * y * s⁻¹ * s := by rw [h]
      _ = s * y := by group
  obtain ⟨r, hrR, hrt⟩ := hd.exists_conj_eq_mul
  have hrW : r ∉ W := by
    intro hrW
    have h1 : r * t * r⁻¹ = t := by rw [hcomm r hrW t htW]; group
    rw [h1] at hrt
    exact hI.ne_one (mul_eq_left.mp hrt.symm)
  have hrr : r * r = z := by
    rcases TF1.Q8Sub.mul_self_eq e hrR with h | h
    · exfalso
      rcases TF1.Q8Sub.eq_of_mul_self_eq_one e hrR h with h' | h'
      · exact hrW (h' ▸ W.one_mem)
      · rw [hzs] at h'
        exact hrW (h' ▸ hzW)
    · exact h.trans hzs
  have hU := hd0.inf_mem_USet
  obtain ⟨-, -, -, -, -, -, hUc, -, hU4⟩ := Sec6Gen.exists_data_of_mem_USet hΩ hU
  obtain ⟨u, huU, huu⟩ := exists_mul_self_eq_of_isCyclic hI inf_le_left hUc
    (S.isPGroup'.to_le (inf_le_right.trans hd.hWS)) hU4
  have huR : u ∈ R := ⟨hd.hWS huU.2, huU.1⟩
  have hsuU : s * u * s⁻¹ ∈ K ⊓ W :=
    ⟨(Subgroup.mem_normalizer_iff.mp hsK u).mp huU.1, (Subgroup.mem_normalizer_iff.mp hsW u).mp huU.2⟩
  have hsuR : s * u * s⁻¹ ∈ R := hconjR s hsS u huR
  have hsqs : ∀ y : G, y * y = z → (s * y * s⁻¹) * (s * y * s⁻¹) = z := by
    intro y hy
    rw [show s * y * s⁻¹ * (s * y * s⁻¹) = s * (y * y) * s⁻¹ by group, hy, hsz,
      mul_inv_cancel_right]
  have hsuu := hsqs u huu
  have hsu : s * u * s⁻¹ = u⁻¹ := by
    have hc : s * u * s⁻¹ * u = u * (s * u * s⁻¹) := hcomm _ hsuU.2 u huU.2
    rcases TF1.Q8Sub.eq_of_comm e huR hsuR (huu.trans hzs.symm) (hsuu.trans hzs.symm) hc with h | h
    · exact absurd ⟨u, huR, hord u huR huu, hcommOf u h⟩ hno
    · exact h
  have hru : r ≠ u := fun h => hrW (h ▸ huU.2)
  have hru' : r ≠ u⁻¹ := fun h => hrW (h ▸ W.inv_mem huU.2)
  set r' : G := s * r * s⁻¹ with hr'
  have hr'R : r' ∈ R := hconjR s hsS r hrR
  have hr'r' : r' * r' = z := hsqs r hrr
  have hr'1 : r' ≠ r := fun h => hno ⟨r, hrR, hord r hrR hrr, hcommOf r h⟩
  have hr'2 : r' ≠ r⁻¹ := by
    intro h
    obtain ⟨h3, h4⟩ := TF1.Q8Sub.anticomm e huR hrR (huu.trans hzs.symm) (hrr.trans hzs.symm) hru hru'
    have hur4 : orderOf (u * r) = 4 := hord _ (R.mul_mem huR hrR) (h3.trans hzs)
    refine hno ⟨u * r, R.mul_mem huR hrR, hur4, hcommOf _ ?_⟩
    calc s * (u * r) * s⁻¹ = (s * u * s⁻¹) * r' := by rw [hr']; group
      _ = u⁻¹ * r⁻¹ := by rw [hsu, h]
      _ = (r * u)⁻¹ := by group
      _ = u * r := by rw [h4, inv_inv]
  set y : G := s * r with hy
  have hyS : y ∈ (S : Subgroup G) := (S : Subgroup G).mul_mem hsS hrR.1
  have hyy : y * y = r' * r := by
    show (s * r) * (s * r) = (s * r * s⁻¹) * r
    rw [hsinv]
    group
  have hy4 : y * y * y * y = z := by
    obtain ⟨h3, -⟩ := TF1.Q8Sub.anticomm e hr'R hrR (hr'r'.trans hzs.symm) (hrr.trans hzs.symm)
      hr'1.symm (fun h => hr'2 (by rw [h, inv_inv]))
    calc y * y * y * y = (y * y) * (y * y) := by group
      _ = z := by rw [hyy, h3, hzs]
  have hyt : y * t * y⁻¹ = t := by
    calc y * t * y⁻¹ = s * (r * t * r⁻¹) * s⁻¹ := by rw [hy]; group
      _ = (s * t * s⁻¹) * (s * z * s⁻¹) := by rw [hrt]; group
      _ = t := by rw [hst, hsz, mul_inv_cancel_right, mul_assoc, hI.sq, mul_one]
  have hyC : y ∈ Subgroup.centralizer ({t} : Set G) := by
    rw [Subgroup.mem_centralizer_singleton_iff]
    calc y * t = y * t * y⁻¹ * y := by group
      _ = t * y := by rw [hyt]
  have hyL : y ∈ Subgroup.normalizer (L : Set G) :=
    hd.tight.centralizer_le_normalizer_member hd.memL hd.invL hyC
  have hVSL := hd.inf_member_eq
  have hyV : ∀ w ∈ V, y * w * y⁻¹ ∈ V := by
    intro w hw
    rw [← hVSL] at hw ⊢
    exact ⟨(S : Subgroup G).mul_mem ((S : Subgroup G).mul_mem hyS hw.1)
      ((S : Subgroup G).inv_mem hyS), (Subgroup.mem_normalizer_iff.mp hyL w).mp hw.2⟩
  obtain ⟨-, -, -, -, -, -, hVc, -, hV4⟩ := Sec6Gen.exists_data_of_mem_USet hΩ hd.memV
  have hV2 : IsPGroup 2 V := S.isPGroup'.to_le (hd.leW.trans hd.hWS)
  obtain ⟨v, hvV, hvv⟩ := exists_mul_self_eq_of_isCyclic hd.invL hd.le_member hVc hV2 hV4
  have hy2 : IsPGroup 2 (Subgroup.zpowers y) := S.isPGroup'.to_le (Subgroup.zpowers_le.mpr hyS)
  have hyN : y ∈ Subgroup.normalizer (V : Set G) := by
    have hle : conjSub y V ≤ V := by
      intro a ha
      rw [mem_conjSub_iff] at ha
      have := hyV _ ha
      simpa [mul_assoc] using this
    exact mem_normalizer_iff_conjSub_eq.mpr (Sec7.conjSub_eq_of_le_self hle)
  have hyNV : Subgroup.zpowers y ≤ Subgroup.normalizer (V : Set G) :=
    Subgroup.zpowers_le.mpr hyN
  have hY2 : IsPGroup 2 ↥(Subgroup.zpowers y ⊔ V) := IsPGroup.to_sup_of_normal_right' hy2 hV2 hyNV
  have hYL : Subgroup.zpowers y ⊔ V ≤ Subgroup.normalizer (L : Set G) :=
    sup_le (Subgroup.zpowers_le.mpr hyL) (hd.le_member.trans Subgroup.le_normalizer)
  obtain ⟨Q, hQ, hQY⟩ := exists_sylow_normalized hY2 hYL
  have hVQ : V ≤ Q := by
    have hVN : V ≤ Subgroup.normalizer (Q : Set G) := fun w hw =>
      mem_normalizer_iff_conjSub_eq.mpr (hQY w (Subgroup.mem_sup_right hw))
    have hQV2 : IsPGroup 2 ↥(V ⊔ Q) := IsPGroup.to_sup_of_normal_right' hV2 hQ.2.1 hVN
    have hle : V ⊔ Q ≤ L := sup_le hd.le_member hQ.1
    have heq : V ⊔ Q = Q := hQ.2.2 _ hle hQV2 le_sup_right
    exact heq ▸ le_sup_left
  have hQR : Q ∈ RSet (CoreAssembly.conjClass K) :=
    mem_RSet_iff.mpr ⟨L, hd.memL, hQ.1, hQ.2.1, hQ.2.2⟩
  obtain ⟨eL⟩ := hd.exists_q8_of_mem_RSet hQR
  have hvQ : v ∈ Q := hVQ hvV
  have htQ : t ∈ Q := hVQ hd.memT
  have hts : ((eL.symm (QuaternionGroup.a 2) : ↥Q) : G) = t := by
    rcases TF1.Q8Sub.eq_of_mul_self_eq_one eL htQ hd.invL.sq with h | h
    · exact absurd h hd.invL.ne_one
    · exact h.symm
  have hyQ : ∀ q ∈ Q, y * q * y⁻¹ ∈ Q := by
    intro q hq
    have h := conj_mem_conjSub (n := y) hq
    rwa [hQY y (Subgroup.mem_sup_left (Subgroup.mem_zpowers y))] at h
  have hyvV : y * v * y⁻¹ ∈ V := hyV v hvV
  have hyvv : (y * v * y⁻¹) * (y * v * y⁻¹) = t := by
    rw [show y * v * y⁻¹ * (y * v * y⁻¹) = y * (v * v) * y⁻¹ by group, hvv, hyt]
  have hyvc : y * v * y⁻¹ * v = v * (y * v * y⁻¹) := hcomm _ (hd.leW hyvV) v (hd.leW hvV)
  have hgv : y * v * y⁻¹ = v ∨ y * v * y⁻¹ = v⁻¹ :=
    TF1.Q8Sub.eq_of_comm eL hvQ (hyQ v hvQ) (hvv.trans hts.symm) (hyvv.trans hts.symm) hyvc
  have h4 := TF1.Q8Sub.pow_four_comm eL hyQ hvQ (hvv.trans hts.symm) hgv
  have hQz : Q ≤ Subgroup.centralizer ({z} : Set G) := fun q hq => by
    rw [Subgroup.mem_centralizer_singleton_iff]
    have := h4 q hq
    rw [hy4] at this
    exact this.symm
  exact hd.tight.not_le_centralizer_of_mem_rSet hd.memL (CoreAssembly.mem_conjClass_self K)
    hd.member_ne hI hQR hQ.1 hQz

theorem exists_conj_eq_of_comm_z {x : G} (hx : x ∈ S19B.sec19BPrime K S W L) {g : G}
    (hsx : g * z * g⁻¹ * x = x * (g * z * g⁻¹)) (hsz : g * z * g⁻¹ * z = z * (g * z * g⁻¹)) :
    ∃ h ∈ Subgroup.centralizer ({x} : Set G), h * z * h⁻¹ = g * z * g⁻¹ := by
  have hI := hd.tight.isUniqueInvolution
  have hss : g * z * g⁻¹ * (g * z * g⁻¹) = 1 := by
    rw [show g * z * g⁻¹ * (g * z * g⁻¹) = g * (z * z) * g⁻¹ by group, hI.sq]
    group
  have hs2 : IsPGroup 2 (Subgroup.zpowers (g * z * g⁻¹)) :=
    (S19Q.isPGroup_zpowers_iff_exists_pow _).mpr ⟨1, by rw [pow_one, sq, hss]⟩
  obtain ⟨S', hd', hx', c, hc, hcs⟩ := hd.exists_sylow_conj hx
    (Subgroup.mem_centralizer_singleton_iff.mpr hsx) (Subgroup.mem_centralizer_singleton_iff.mpr hsz)
    hs2
  have hcx : c * x = x * c := Subgroup.mem_centralizer_singleton_iff.mp hc.1
  have hcz : c * z = z * c := Subgroup.mem_centralizer_singleton_iff.mp hc.2
  have e₂ : c * (g * z * g⁻¹) * c⁻¹ = (c * g) * z * (c * g)⁻¹ := by group
  rw [e₂] at hcs
  have hsx₂ : (c * g) * z * (c * g)⁻¹ * x = x * ((c * g) * z * (c * g)⁻¹) := by
    rw [← e₂]
    calc c * (g * z * g⁻¹) * c⁻¹ * x = c * (g * z * g⁻¹) * (c⁻¹ * x * c) * c⁻¹ := by group
      _ = c * (g * z * g⁻¹) * x * c⁻¹ := by
          rw [show c⁻¹ * x * c = x by rw [mul_assoc, ← hcx, inv_mul_cancel_left]]
      _ = c * (x * (g * z * g⁻¹)) * c⁻¹ := by rw [mul_assoc c, hsx, ← mul_assoc]
      _ = x * (c * (g * z * g⁻¹) * c⁻¹) := by
          rw [show c * (x * (g * z * g⁻¹)) * c⁻¹ = (c * x) * (g * z * g⁻¹) * c⁻¹ by group, hcx]
          group
  have hsz₂ : (c * g) * z * (c * g)⁻¹ * z = z * ((c * g) * z * (c * g)⁻¹) := by
    rw [← e₂]
    calc c * (g * z * g⁻¹) * c⁻¹ * z = c * (g * z * g⁻¹) * (c⁻¹ * z * c) * c⁻¹ := by group
      _ = c * (g * z * g⁻¹) * z * c⁻¹ := by
          rw [show c⁻¹ * z * c = z by rw [mul_assoc, ← hcz, inv_mul_cancel_left]]
      _ = c * (z * (g * z * g⁻¹)) * c⁻¹ := by rw [mul_assoc c, hsz, ← mul_assoc]
      _ = z * (c * (g * z * g⁻¹) * c⁻¹) := by
          rw [show c * (z * (g * z * g⁻¹)) * c⁻¹ = (c * z) * (g * z * g⁻¹) * c⁻¹ by group, hcz]
          group
  have key : ∃ h ∈ Subgroup.centralizer ({x} : Set G), h * z * h⁻¹ = (c * g) * z * (c * g)⁻¹ := by
    have hzt : z * t = t * z := hd.toTightSylowData.comm_of_mem z hd.mem_W_z t hd.mem_W
    rcases hd'.conj_t_eq_or_of_le_normalizer hd'.le_normalizer_W hcs with ht | ht
    · have hst : (c * g) * z * (c * g)⁻¹ * t = t * ((c * g) * z * (c * g)⁻¹) := by
        calc (c * g) * z * (c * g)⁻¹ * t
            = ((c * g) * z * (c * g)⁻¹) * t * ((c * g) * z * (c * g)⁻¹)⁻¹ *
              ((c * g) * z * (c * g)⁻¹) := by group
          _ = t * ((c * g) * z * (c * g)⁻¹) := by rw [ht]
      exact hd'.exists_conj_eq_of_comm_t hx' hsx₂ hsz₂ hst
    · have hsne : (c * g) * z * (c * g)⁻¹ ≠ z := by
        intro h
        rw [h] at ht
        have h1 : z * t * z⁻¹ = t := by rw [hzt, mul_inv_cancel_right]
        rw [h1] at ht
        exact hI.ne_one (mul_eq_left.mp ht.symm)
      have hss₂ : (c * g) * z * (c * g)⁻¹ * ((c * g) * z * (c * g)⁻¹) = 1 := by
        rw [show (c * g) * z * (c * g)⁻¹ * ((c * g) * z * (c * g)⁻¹) =
          (c * g) * (z * z) * (c * g)⁻¹ by group, hI.sq]
        group
      by_cases hw : ∃ w ∈ (S' : Subgroup G) ⊓ K, orderOf w = 4 ∧
          w * ((c * g) * z * (c * g)⁻¹) = ((c * g) * z * (c * g)⁻¹) * w
      · obtain ⟨w, hwR, hw4, hws⟩ := hw
        exact hd'.exists_conj_eq_of_comm_u hx' hsx₂ hsne hwR.2 hw4 hws
      · exact (hd'.false_of_outer hcs hss₂ ht hw).elim
  obtain ⟨h, hh, he⟩ := key
  refine ⟨c⁻¹ * h, Subgroup.mul_mem _ (Subgroup.inv_mem _ hc.1) hh, ?_⟩
  calc c⁻¹ * h * z * (c⁻¹ * h)⁻¹ = c⁻¹ * (h * z * h⁻¹) * c := by group
    _ = c⁻¹ * ((c * g) * z * (c * g)⁻¹) * c := by rw [he]
    _ = g * z * g⁻¹ := by group

end TightSylowDataT

variable {R : Subgroup G} {S₀ : Sylow 2 R} {t₀ : G} {T : Sylow 2 G}

theorem TightSylowStd.comm_of_mem_of_inf_core_le (h : TightSylowStd R S₀ t₀ T) {P : Subgroup G}
    (hP2 : IsPGroup 2 P) (hS₀P : (T : Subgroup G) ⊓ tightCore R ≤ P) {p : G} (hp : p ∈ P) :
    p * t₀ = t₀ * p := by
  apply h.comm_of_mem_normalizer_inf_core
  rw [h.inf_core_eq] at hS₀P ⊢
  have hS2 : IsSylow2Of ((S₀ : Subgroup R).map R.subtype) (tightCore R) := h.sylow_core
  obtain ⟨Q₀, hQ₀⟩ := hS2.exists_sylow
  rw [← hQ₀] at hS₀P ⊢
  have hle : conjSub p ((Q₀ : Subgroup (tightCore R)).map (tightCore R).subtype) ≤ P := by
    intro a ha
    rw [mem_conjSub_iff] at ha
    have := P.mul_mem (P.mul_mem hp (hS₀P ha)) (P.inv_mem hp)
    simpa [mul_assoc] using this
  exact mem_normalizer_iff_conjSub_eq.mpr (h.datum.sylow_eq h.edgeless Q₀ hP2 hS₀P hle)

theorem tightF1S_holds {IH : ℕ → Prop} : TightF1S IH := by
  intro G _ _ _ _ _ R S t T W L t' V _ h hd x hx _ g hg
  have hss : g * t * g⁻¹ * (g * t * g⁻¹) = 1 := by
    rw [show g * t * g⁻¹ * (g * t * g⁻¹) = g * (t * t) * g⁻¹ by group, t_mul_t h.datum]
    group
  have hs2 : IsPGroup 2 (Subgroup.zpowers (g * t * g⁻¹)) :=
    (S19Q.isPGroup_zpowers_iff_exists_pow _).mpr ⟨1, by rw [pow_one, sq, hss]⟩
  set H : Subgroup G := Subgroup.centralizer ({x} : Set G) with hH
  obtain ⟨P, hP, hTP⟩ := IsSylow2In.exists_ge
    (T.isPGroup'.to_le inf_le_left : IsPGroup 2 ↥((T : Subgroup G) ⊓ H)) inf_le_right
  obtain ⟨c, hcH, hsc⟩ := Sec7.exists_conj_le_of_isSylow2In hP hs2 (Subgroup.zpowers_le.mpr hg)
  have hcs : c⁻¹ * (g * t * g⁻¹) * c ∈ P := mem_conjSub_iff.mp (hsc (Subgroup.mem_zpowers _))
  have hS₀P : (T : Subgroup G) ⊓ tightCore R ≤ P := fun r hr =>
    hTP ⟨hr.1, Subgroup.mem_centralizer_singleton_iff.mpr
      (Subgroup.mem_centralizer_iff.mp hx.1.1.2 r hr)⟩
  have hct := h.comm_of_mem_of_inf_core_le hP.2.1 hS₀P hcs
  have hcx : c * x = x * c := Subgroup.mem_centralizer_singleton_iff.mp hcH
  have hgx : g * t * g⁻¹ * x = x * (g * t * g⁻¹) :=
    Subgroup.mem_centralizer_singleton_iff.mp hg
  have e₁ : c⁻¹ * (g * t * g⁻¹) * c = (c⁻¹ * g) * t * (c⁻¹ * g)⁻¹ := by group
  rw [e₁] at hct
  have hcx' : c⁻¹ * x = x * c⁻¹ := by
    calc c⁻¹ * x = c⁻¹ * (x * c) * c⁻¹ := by group
      _ = c⁻¹ * (c * x) * c⁻¹ := by rw [hcx]
      _ = x * c⁻¹ := by group
  have hsx : (c⁻¹ * g) * t * (c⁻¹ * g)⁻¹ * x = x * ((c⁻¹ * g) * t * (c⁻¹ * g)⁻¹) := by
    rw [← e₁]
    calc c⁻¹ * (g * t * g⁻¹) * c * x = c⁻¹ * (g * t * g⁻¹) * (c * x) := by group
      _ = c⁻¹ * (g * t * g⁻¹) * (x * c) := by rw [hcx]
      _ = c⁻¹ * ((g * t * g⁻¹) * x) * c := by group
      _ = c⁻¹ * (x * (g * t * g⁻¹)) * c := by rw [hgx]
      _ = (c⁻¹ * x) * (g * t * g⁻¹) * c := by group
      _ = (x * c⁻¹) * (g * t * g⁻¹) * c := by rw [hcx']
      _ = x * (c⁻¹ * (g * t * g⁻¹) * c) := by group
  obtain ⟨h₁, hh₁, he₁⟩ := hd.exists_conj_eq_of_comm_z hx hsx hct
  refine ⟨c * h₁, Subgroup.mul_mem _ hcH hh₁, ?_⟩
  calc c * h₁ * t * (c * h₁)⁻¹ = c * (h₁ * t * h₁⁻¹) * c⁻¹ := by group
    _ = c * ((c⁻¹ * g) * t * (c⁻¹ * g)⁻¹) * c⁻¹ := by rw [he₁]
    _ = g * t * g⁻¹ := by group

section Gold


theorem tightC19_11bS_holds {IH : ℕ → Prop} : TightC19_11bS IH :=
  tightC19_11bS_of_F1 tightF1S_holds

theorem tightLargeEdgeS_holds (n : ℕ) : TightLargeEdgeS n :=
  tightLargeEdgeS_of_core tightC19_11bS_holds n

end Gold

end CFSG.ClassicalInvolution.Q3
