module

public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.A5.S10R
public import Certificates.Certificate17027
public import Certificates.Certificate5952
public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.A5.S10S

public section

namespace CFSG.QuasithinUnique.A5

open CFSG.Open CFSG.Quasithin CFSG.QuasithinUnique CFSG.QuasithinUnique.DoubleA3
  CFSG.QuasithinUnique.A5.Delta5 CFSG.QuasithinUnique.A5.Action CFSG.QuasithinUnique.A5.Split

namespace Sec

variable {G : Type} [Group G] [Finite G] {T M H S L : Subgroup G} {C : StdCfg T M H S L}
  (X : Sec C)

include X

omit X in
theorem zp_eq_one_iff (C : StdCfg T M H S L) (t : ZMod 2) : C.zp t = 1 ↔ t = 0 := by
  rcases zmod2_cases t with rfl | rfl
  · simp [StdCfg.zp]
  · simp only [StdCfg.zp]
    constructor
    · intro h
      exact absurd (by simpa using h) C.zU_ne_one
    · intro h
      exact absurd h (by decide)

variable {X} {i : G} {w : V4}

theorem IsRefl.comm_e (h : X.IsRefl i w) (hw : quadHyp w = 1)
    (hcent : ∀ q ∈ X.QPl w hw, i * q * i⁻¹ = q) {e : G} {c : GL (Fin 4) (ZMod 2)}
    (heM : e ∈ M) (he3 : e ^ 3 = 1) (hec : X.rg e = c)
    (hcfix : ∀ x, inPl' w x → (c : Mat4).mulVec x = x)
    (hcPi : ∀ a, inPl w a → inPl w ((c : Mat4).mulVec a))
    (hcBf : ∀ x, Bf ((c : Mat4).mulVec x) w = Bf x w) : i * e * i⁻¹ = e := by
  have hi : i⁻¹ = i := h.inv_eq
  have hiM : i ∈ M := h.1
  have hcw : (c : Mat4).mulVec w = w := hcfix w (pl'_w w hw)
  have hcomm : (c : Mat4) * ((X.rg i : GL (Fin 4) (ZMod 2)) : Mat4) =
      ((X.rg i : GL (Fin 4) (ZMod 2)) : Mat4) * (c : Mat4) := comm_refl h.2.2 hcw hcBf
  have hcomm' : c * X.rg i = X.rg i * c := Units.ext hcomm
  set e' : G := i * e * i⁻¹ with he'
  have he'M : e' ∈ M := M.mul_mem (M.mul_mem hiM heM) (M.inv_mem hiM)
  have hrge' : X.rg e' = c := by
    rw [he', X.rg_mul (M.mul_mem hiM heM) (M.inv_mem hiM), X.rg_mul hiM heM, X.rg_inv hiM, hec,
      ← hcomm']
    group
  set a : G := e⁻¹ * e' with ha
  have haM : a ∈ M := M.mul_mem (M.inv_mem heM) he'M
  have haP : a ∈ borelP M L := by
    refine (X.rg_eq_one_iff haM).mp ?_
    rw [ha, X.rg_mul (M.inv_mem heM) he'M, X.rg_inv heM, hec, hrge']
    exact inv_mul_cancel c
  have hth_e : ∀ p ∈ borelP M L, e * p * e⁻¹ ∈ borelP M L ∧
      X.th (e * p * e⁻¹) = (c : Mat4).mulVec (X.th p) := by
    intro p hp
    obtain ⟨h1, h2⟩ := X.th_conj heM hp
    rw [hec] at h2
    exact ⟨h1, h2⟩
  have hnormY : ∀ y ∈ X.QPl w hw, e * y * e⁻¹ ∈ X.QPl w hw := by
    intro y hy
    have hy' : y ∈ borelP M L ∧ inPl w (X.th y) := hy
    obtain ⟨h1, h2⟩ := hth_e y hy'.1
    show e * y * e⁻¹ ∈ borelP M L ∧ inPl w (X.th (e * y * e⁻¹))
    exact ⟨h1, by rw [h2]; exact hcPi _ hy'.2⟩
  have haY : ∀ y ∈ X.QPl w hw, a * y * a⁻¹ = y := by
    intro y hy
    have h1' : i⁻¹ * y * i = y := by
      calc i⁻¹ * y * i = i⁻¹ * (i * y * i⁻¹) * i := by rw [hcent y hy]
        _ = y := by group
    have h3 : e' * y * e'⁻¹ = e * y * e⁻¹ := by
      calc e' * y * e'⁻¹ = i * e * (i⁻¹ * y * i) * e⁻¹ * i⁻¹ := by rw [he']; group
        _ = i * (e * y * e⁻¹) * i⁻¹ := by rw [h1']; group
        _ = e * y * e⁻¹ := hcent _ (hnormY y hy)
    calc a * y * a⁻¹ = e⁻¹ * (e' * y * e'⁻¹) * e := by rw [ha]; group
      _ = y := by rw [h3]; group
  have haY' : ∀ y ∈ X.QPl' w hw, a * y * a⁻¹ = y := by
    intro y hy
    have hy' : y ∈ borelP M L ∧ inPl' w (X.th y) := hy
    obtain ⟨h1, h2⟩ := h.th_conj hy'.1
    have hy'' : inPl' w (X.th (i * y * i⁻¹)) := by
      rw [h2]
      exact pl'_refl w _ hw hy'.2
    have hey := centralizes_QPl' heM he3 hec hcfix hy'.1 hy'.2
    have hey'' := centralizes_QPl' heM he3 hec hcfix h1 hy''
    have hyy : i⁻¹ * y * i = i * y * i⁻¹ := by rw [hi]
    have h4 : e' * y * e'⁻¹ = y := by
      calc e' * y * e'⁻¹ = i * e * (i⁻¹ * y * i) * e⁻¹ * i⁻¹ := by rw [he']; group
        _ = i * (e * (i * y * i⁻¹) * e⁻¹) * i⁻¹ := by rw [hyy]; group
        _ = i * (i * y * i⁻¹) * i⁻¹ := by rw [hey'']
        _ = (i * i) * y * (i * i)⁻¹ := by group
        _ = y := by rw [h.2.1]; group
    calc a * y * a⁻¹ = e⁻¹ * (e' * y * e'⁻¹) * e := by rw [ha]; group
      _ = e⁻¹ * y * e := by rw [h4]
      _ = y := by
        calc e⁻¹ * y * e = e⁻¹ * (e * y * e⁻¹) * e := by rw [hey]
          _ = y := by group
  have hpl' : inPl' w (X.th a) := by
    refine pl_perp w (X.th a) hw ?_
    intro a1 ha1
    obtain ⟨y, hyP, hyth⟩ := X.th_exists a1
    have hyY : y ∈ X.QPl w hw := ⟨hyP, by rw [hyth]; exact ha1⟩
    have hc := X.comm_th haP hyP
    have h0 : a * y * a⁻¹ * y⁻¹ = 1 := by rw [haY y hyY]; group
    rw [h0, hyth] at hc
    rw [Bf_comm]
    exact (zp_eq_one_iff C _).mp hc.symm
  have hpl : inPl w (X.th a) := by
    refine pl_perp' w (X.th a) hw ?_
    intro x hx
    obtain ⟨y, hyP, hyth⟩ := X.th_exists x
    have hyY : y ∈ X.QPl' w hw := ⟨hyP, by rw [hyth]; exact hx⟩
    have hc := X.comm_th haP hyP
    have h0 : a * y * a⁻¹ * y⁻¹ = 1 := by rw [haY' y hyY]; group
    rw [h0, hyth] at hc
    exact (zp_eq_one_iff C _).mp hc.symm
  have ha0 : X.th a = 0 := pl_inf w _ hw hpl hpl'
  rcases (X.th_eq_zero_iff haP).mp ha0 with ha1 | ha1
  ·
    calc i * e * i⁻¹ = e' := rfl
      _ = e * (e⁻¹ * e') := by group
      _ = e := by rw [← ha, ha1, mul_one]
  · exfalso
    have he'eq : e' = e * C.zU := by
      calc e' = e * (e⁻¹ * e') := by group
        _ = e * C.zU := by rw [← ha, ha1]
    have he'3 : e' ^ 3 = 1 := by
      rw [he', conj_pow, he3]
      group
    have hcom : Commute e C.zU := (X.zU_comm_M heM).symm
    have : (e * C.zU) ^ 3 = C.zU := by
      rw [hcom.mul_pow, he3, one_mul, pow_three, ← mul_assoc, C.zU_mul_self, one_mul]
    rw [he'eq, this] at he'3
    exact C.zU_ne_one he'3

theorem IsRefl.exists_twoThree
    (h : X.IsRefl i w) (hw : quadHyp w = 1)
    (hcent : ∀ q ∈ X.QPl w hw, i * q * i⁻¹ = q) :
    ∃ (Y : Subgroup G) (c : G), IsTwoThree Y c ∧ Y ≤ Subgroup.centralizer ({i} : Set G) ∧
      c ∈ Subgroup.centralizer ({i} : Set G) ∧ C.zU ∈ Y := by
  obtain ⟨c, hcO, hc3, hc1, hcfix, hcPi, hcsurj, hcBf⟩ := exists_c hw
  obtain ⟨e, heW, he3, herg⟩ := X.exists_lift_W hcO hc3
  have heM : e ∈ M := pResidual2_le heW
  have hie : i * e * i⁻¹ = e := h.comm_e hw hcent heM he3 herg hcfix hcPi hcBf
  have h1 : e * e = e⁻¹ := (inv_eq_of_mul_eq_one_right (by rw [← pow_three]; exact he3)).symm
  have h2 : e⁻¹ * e⁻¹ = e := by
    rw [← h1]
    calc e * e * (e * e) = e * (e * e * e) := by group
      _ = e := by rw [← pow_three', he3, mul_one]
  have hth_e : ∀ p ∈ borelP M L, e * p * e⁻¹ ∈ borelP M L ∧
      X.th (e * p * e⁻¹) = (c : Mat4).mulVec (X.th p) := by
    intro p hp
    obtain ⟨h1, h2⟩ := X.th_conj heM hp
    rw [herg] at h2
    exact ⟨h1, h2⟩
  have hnormY : ∀ y ∈ X.QPl w hw, e * y * e⁻¹ ∈ X.QPl w hw := by
    intro y hy
    have hy' : y ∈ borelP M L ∧ inPl w (X.th y) := hy
    obtain ⟨h1, h2⟩ := hth_e y hy'.1
    show e * y * e⁻¹ ∈ borelP M L ∧ inPl w (X.th (e * y * e⁻¹))
    exact ⟨h1, by rw [h2]; exact hcPi _ hy'.2⟩
  have hnormY' : ∀ y ∈ X.QPl w hw, e⁻¹ * y * e ∈ X.QPl w hw := by
    intro y hy
    have : e⁻¹ * y * e = e * (e * y * e⁻¹) * e⁻¹ := by
      calc e⁻¹ * y * e = (e * e) * y * (e⁻¹ * e⁻¹) := by rw [h1, h2]
        _ = e * (e * y * e⁻¹) * e⁻¹ := by group
    rw [this]
    exact hnormY _ (hnormY y hy)
  have hP2 : IsPGroup 2 ↥(borelP M L) :=
    CFSG.RankThreeCoreUniqueness.Helpers.pCoreOf_isPGroup 2 _
  have hYP : X.QPl w hw ≤ borelP M L := fun y hy => (hy : y ∈ borelP M L ∧ _).1
  have hne : e ≠ 1 := by
    intro h1
    apply hc1
    rw [← herg, h1, X.rg_one]
  have hnorm : e ∈ Subgroup.normalizer ((X.QPl w hw : Subgroup G) : Set G) := by
    rw [Subgroup.mem_normalizer_iff]
    intro y
    refine ⟨fun hy => hnormY y hy, fun hy => ?_⟩
    have := hnormY' _ hy
    rwa [show e⁻¹ * (e * y * e⁻¹) * e = y by group] at this
  have hgen : X.QPl w hw ≤ ⁅X.QPl w hw, Subgroup.zpowers e⁆ := by
    obtain ⟨a1, a2, ha1, ha2, ha10, ha20, ha12, hall, -⟩ := pl_basis w hw
    obtain ⟨b1, hb1, hb1e⟩ := hcsurj a1 ha1
    obtain ⟨b2, hb2, hb2e⟩ := hcsurj a2 ha2
    obtain ⟨y1, hy1P, hy1th⟩ := X.th_exists b1
    obtain ⟨y2, hy2P, hy2th⟩ := X.th_exists b2
    have hy1Y : y1 ∈ X.QPl w hw := ⟨hy1P, by rw [hy1th]; exact hb1⟩
    have hy2Y : y2 ∈ X.QPl w hw := ⟨hy2P, by rw [hy2th]; exact hb2⟩
    set K0 := ⁅X.QPl w hw, Subgroup.zpowers e⁆ with hK0
    have hκ : ∀ y ∈ X.QPl w hw, y * e * y⁻¹ * e⁻¹ ∈ K0 := by
      intro y hy
      have := Subgroup.commutator_mem_commutator hy (Subgroup.mem_zpowers e)
      rwa [commutatorElement_def] at this
    have hκP : ∀ y ∈ X.QPl w hw, y * e * y⁻¹ * e⁻¹ ∈ borelP M L := by
      intro y hy
      have hy' : y ∈ borelP M L := (hy : y ∈ borelP M L ∧ _).1
      have : y * e * y⁻¹ * e⁻¹ = y * (e * y⁻¹ * e⁻¹) := by group
      rw [this]
      exact mul_mem hy' (hth_e y⁻¹ (inv_mem hy')).1
    have hκth : ∀ y ∈ X.QPl w hw, X.th (y * e * y⁻¹ * e⁻¹) =
        X.th y + (c : Mat4).mulVec (X.th y) := by
      intro y hy
      have hy' : y ∈ borelP M L := (hy : y ∈ borelP M L ∧ _).1
      have : y * e * y⁻¹ * e⁻¹ = y * (e * y⁻¹ * e⁻¹) := by group
      rw [this, X.th_mul hy' (hth_e y⁻¹ (inv_mem hy')).1, (hth_e y⁻¹ (inv_mem hy')).2,
        X.th_inv hy']
    set κ1 := y1 * e * y1⁻¹ * e⁻¹ with hκ1
    set κ2 := y2 * e * y2⁻¹ * e⁻¹ with hκ2
    have hκ1th : X.th κ1 = a1 := by rw [hκ1, hκth y1 hy1Y, hy1th, hb1e]
    have hκ2th : X.th κ2 = a2 := by rw [hκ2, hκth y2 hy2Y, hy2th, hb2e]
    have hκ1K : κ1 ∈ K0 := hκ y1 hy1Y
    have hκ2K : κ2 ∈ K0 := hκ y2 hy2Y
    have hκ1P : κ1 ∈ borelP M L := hκP y1 hy1Y
    have hκ2P : κ2 ∈ borelP M L := hκP y2 hy2Y
    have hzK : C.zU ∈ K0 := by
      have hc12 := X.comm_th hκ1P hκ2P
      rw [hκ1th, hκ2th, pl_Bf1 w a1 a2 hw ha1 ha2 ha10 ha20 ha12] at hc12
      have hz1 : C.zp 1 = C.zU := by simp [StdCfg.zp]
      rw [hz1] at hc12
      rw [← hc12]
      exact K0.mul_mem (K0.mul_mem (K0.mul_mem hκ1K hκ2K) (K0.inv_mem hκ1K)) (K0.inv_mem hκ2K)
    intro y hy
    have hy' : y ∈ borelP M L ∧ inPl w (X.th y) := hy
    have hfib : ∀ κ : G, κ ∈ K0 → κ ∈ borelP M L → X.th κ = X.th y → y ∈ K0 := by
      intro κ hκK hκP hth
      rcases X.th_fiber hy'.1 hκP hth.symm with hh | hh
      · rw [hh]; exact hκK
      · rw [hh]; exact K0.mul_mem hκK hzK
    rcases hall _ hy'.2 with h0 | h0 | h0 | h0
    · rcases (X.th_eq_zero_iff hy'.1).mp h0 with rfl | rfl
      · exact one_mem _
      · exact hzK
    · exact hfib κ1 hκ1K hκ1P (by rw [hκ1th, h0])
    · exact hfib κ2 hκ2K hκ2P (by rw [hκ2th, h0])
    · refine hfib (κ1 * κ2) (K0.mul_mem hκ1K hκ2K) (mul_mem hκ1P hκ2P) ?_
      rw [X.th_mul hκ1P hκ2P, hκ1th, hκ2th, h0]
  have hle : ⁅X.QPl w hw, Subgroup.zpowers e⁆ ≤ X.QPl w hw := by
    rw [Subgroup.commutator_le]
    intro y hy g hg
    rw [commutatorElement_def]
    have hgN : g ∈ Subgroup.normalizer ((X.QPl w hw : Subgroup G) : Set G) :=
      (Subgroup.zpowers_le.mpr hnorm) hg
    have h1 : g * y⁻¹ * g⁻¹ ∈ X.QPl w hw :=
      (Subgroup.mem_normalizer_iff.mp hgN y⁻¹).mp ((X.QPl w hw).inv_mem hy)
    have : y * g * y⁻¹ * g⁻¹ = y * (g * y⁻¹ * g⁻¹) := by group
    rw [this]
    exact (X.QPl w hw).mul_mem hy h1
  refine ⟨X.QPl w hw, e, ⟨hP2.to_le hYP, orderOf_eq_prime he3 hne, hnorm,
    le_antisymm hle hgen⟩, ?_, ?_, ?_⟩
  · intro y hy
    rw [Subgroup.mem_centralizer_iff]
    intro g hg
    rw [Set.mem_singleton_iff] at hg
    subst hg
    calc g * y = (g * y * g⁻¹) * g := by group
      _ = y * g := by rw [hcent y hy]
  · rw [Subgroup.mem_centralizer_iff]
    intro g hg
    rw [Set.mem_singleton_iff] at hg
    subst hg
    calc g * e = (g * e * g⁻¹) * g := by group
      _ = e * g := by rw [hie]
  · exact ⟨X.zU_mem_P, by rw [X.th_zU]; exact Or.inl rfl⟩

theorem dichotomy_aux
    {i u : G} (hiM : i ∈ M) (hiWS : i ∉ pResidualOf 2 M ⊔ S) (hi2 : i ^ 2 = 1)
    (huP : u ∈ borelP M L) (huZ : u ∉ centerOf (borelP M L)) (hu2 : u ^ 2 = 1) :
    (∃ (Y : Subgroup G) (c : G), IsTwoThree Y c ∧ Y ≤ Subgroup.centralizer ({i} : Set G) ∧
      c ∈ Subgroup.centralizer ({i} : Set G) ∧ C.zU ∈ Y) ∨
    ∃ m ∈ M, m⁻¹ * i * m ∈ centralizerElem u := by
  have hii : i * i = 1 := by rw [← pow_two]; exact hi2
  have hgO : X.rg i ∈ O4PlusTwo := X.rg_mem_O4 hiM
  have hgg : X.rg i * X.rg i = 1 := by rw [← X.rg_mul hiM hiM, hii, X.rg_one]
  rcases invol_cases hgO hgg with ⟨V, hV, hcube⟩ | ⟨w, hw, hx⟩
  · exfalso
    apply hiWS
    obtain ⟨s, hsS, hsV⟩ := X.exists_S_of_VSL hV
    have hsM : s ∈ M := C.S_le_M hsS
    have heO : X.rg i * X.rg s ∈ O4PlusTwo := mul_mem hgO (X.rg_mem_O4 hsM)
    have he3 : (X.rg i * X.rg s) ^ 3 = 1 := by
      apply Units.ext
      rw [Units.val_pow_eq_pow_val, Units.val_mul, hsV]
      simpa using hcube
    obtain ⟨d, hdW, hd3, hdrg⟩ := X.exists_lift_W heO he3
    have hdM : d ∈ M := pResidual2_le hdW
    have hP : d⁻¹ * i * s ∈ borelP M L := by
      refine (X.rg_eq_one_iff (M.mul_mem (M.mul_mem (M.inv_mem hdM) hiM) hsM)).mp ?_
      rw [X.rg_mul (M.mul_mem (M.inv_mem hdM) hiM) hsM, X.rg_mul (M.inv_mem hdM) hiM,
        X.rg_inv hdM, hdrg]
      group
    have : i = d * ((d⁻¹ * i * s) * s⁻¹) := by group
    rw [this]
    exact mul_mem (Subgroup.mem_sup_left hdW)
      (Subgroup.mem_sup_right (mul_mem (X.P_le_S hP) (inv_mem hsS)))
  · have hrefl : X.IsRefl i w := ⟨hiM, hii, hx⟩
    by_cases hno : ∃ p ∈ borelP M L, p ∉ centerOf (borelP M L) ∧ p ^ 2 = 1 ∧ i * p * i⁻¹ = p
    · right
      obtain ⟨p, hpP, hpZ, hp2, hpi⟩ := hno
      obtain ⟨m, hmM, hmp⟩ := X.trans_P hpP huP hpZ huZ hp2 hu2
      refine ⟨m, hmM, ?_⟩
      show m⁻¹ * i * m ∈ Subgroup.centralizer ({u} : Set G)
      rw [Subgroup.mem_centralizer_iff]
      intro g hg
      rw [Set.mem_singleton_iff] at hg
      rw [hg]
      have hpc : i * p = p * i := by
        calc i * p = (i * p * i⁻¹) * i := by group
          _ = p * i := by rw [hpi]
      calc u * (m⁻¹ * i * m) = (m⁻¹ * p * m) * (m⁻¹ * i * m) := by rw [hmp]
        _ = m⁻¹ * (p * i) * m := by group
        _ = m⁻¹ * (i * p) * m := by rw [hpc]
        _ = (m⁻¹ * i * m) * (m⁻¹ * p * m) := by group
        _ = (m⁻¹ * i * m) * u := by rw [hmp]
    · left
      push Not at hno
      exact hrefl.exists_twoThree hw (fun q hq => hrefl.cent_QPl hw hno hq)

end Sec

end CFSG.QuasithinUnique.A5
