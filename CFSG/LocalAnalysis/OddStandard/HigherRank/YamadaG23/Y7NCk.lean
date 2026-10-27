module

public import CFSG.LocalAnalysis.OddStandard.HigherRank.YamadaG23.Y7S3
public import CFSG.LocalAnalysis.OddStandard.HigherRank.YamadaG23.Y31SylConj

public section

namespace CFSG.OddStandard.HigherRank.YamadaG23

open Subgroup CFSG.Open CFSG.OddStandard.HigherRank.G2Three
  CFSG.OddStandard.HigherRank.G2Three.Sec1 CFSG.GH74.GLS
open scoped commutatorElement Pointwise

variable {G : Type} [Group G] [Finite G] {L : Subgroup G}

theorem y7n_cent_two_le_M6 {c : Ctx7 G L} (h7 : c.Upto79) {Z : Subgroup G} (hZ : IsPGroup 2 Z)
    (hZc : ∀ z ∈ Z, ∀ m ∈ M6 c.e, z * m = m * z) : Z ≤ M6 c.e := by
  obtain ⟨⟨⟨⟨⟨⟨⟨⟨h71, h72⟩, _h73⟩, h74⟩, _h75⟩, _h76⟩, _h77⟩, _h78⟩, _h79⟩ := h7
  have hC6p : IsPGroup 2 (C6 c.e) := h74.2.2.1
  have hM6p : IsPGroup 2 (M6 c.e) := hC6p.to_le (show M6 c.e ≤ C6 c.e from inf_le_left)
  have hA_le_M6 : c.s.fr.A ≤ M6 c.e := by
    rw [← h71.2.1.2.1]
    exact inf_le_right
  have hV1_le_M6 : V1 c.e ≤ M6 c.e := by
    rw [← h72.2.2.1.1]
    exact Subgroup.commutator_le.mpr fun a ha b hb => by
      rw [commutatorElement_def]
      exact (M6 c.e).mul_mem ((M6 c.e).mul_mem ((M6 c.e).mul_mem ha hb)
        ((M6 c.e).inv_mem ha)) ((M6 c.e).inv_mem hb)
  have hAV1_le_M6 : AV1 c.e ≤ M6 c.e := sup_le hA_le_M6 hV1_le_M6
  have hZcentM6 : Z ≤ Subgroup.centralizer (M6 c.e : Set G) := fun z hz =>
    Subgroup.mem_centralizer_iff.mpr fun m hm => (hZc z hz m hm).symm
  have hZcentAV1 : Z ≤ Subgroup.centralizer (AV1 c.e : Set G) := fun z hz =>
    Subgroup.mem_centralizer_iff.mpr fun a ha => (hZc z hz a (hAV1_le_M6 ha)).symm
  have hZcentV1 : Z ≤ Subgroup.centralizer (V1 c.e : Set G) := fun z hz =>
    Subgroup.mem_centralizer_iff.mpr fun v hv => (hZc z hz v (hV1_le_M6 hv)).symm
  have hZ_le_W : Z ≤ centralizerSection (AV1 c.e) (V1 c.e) := fun z hz =>
    ⟨Subgroup.centralizer_le_normalizer (AV1 c.e : Set G) (hZcentAV1 hz),
     Subgroup.centralizer_le_normalizer (V1 c.e : Set G) (hZcentV1 hz),
     fun k hk => by
       rw [commutatorElement_eq_one_iff_mul_comm.mpr (hZc z hz k (hAV1_le_M6 hk)).symm]
       exact (V1 c.e).one_mem⟩
  have hM6_le_W : M6 c.e ≤ centralizerSection (AV1 c.e) (V1 c.e) :=
    (show M6 c.e ≤ C6 c.e from inf_le_left).trans h74.2.1
  have hZnormM6 : Z ≤ Subgroup.normalizer (M6 c.e : Set G) :=
    hZcentM6.trans (Subgroup.centralizer_le_normalizer (M6 c.e : Set G))
  have hQp : IsPGroup 2 (Z ⊔ M6 c.e : Subgroup G) := hZ.to_sup_of_normal_right' hM6p hZnormM6
  have hQ_le_W : (Z ⊔ M6 c.e) ≤ centralizerSection (AV1 c.e) (V1 c.e) :=
    sup_le hZ_le_W hM6_le_W
  obtain ⟨w, hwW, hconjC6⟩ := exists_conj_le_isSylowIn h74.2 hQp hQ_le_W
  have hQ_le_cent : (Z ⊔ M6 c.e) ≤ Subgroup.centralizer (V1 c.e : Set G) :=
    sup_le hZcentV1 (show M6 c.e ≤ Subgroup.centralizer (V1 c.e : Set G) from inf_le_right)
  have hW_cent_conj : ∀ w ∈ centralizerSection (AV1 c.e) (V1 c.e),
      ∀ x ∈ Subgroup.centralizer (V1 c.e : Set G),
      w * x * w⁻¹ ∈ Subgroup.centralizer (V1 c.e : Set G) := by
    intro w hw x hx
    obtain ⟨_hwAV, hwV, _hwcomm⟩ := hw
    rw [Subgroup.mem_centralizer_iff] at hx ⊢
    intro v hv
    have hwv : w⁻¹ * v * w ∈ V1 c.e := by
      have h := (Subgroup.mem_normalizer_iff.mp (Subgroup.inv_mem _ hwV) v).mp hv
      simpa using h
    calc v * (w * x * w⁻¹) = w * ((w⁻¹ * v * w) * x) * w⁻¹ := by group
      _ = w * (x * (w⁻¹ * v * w)) * w⁻¹ := by rw [hx (w⁻¹ * v * w) hwv]
      _ = (w * x * w⁻¹) * v := by group
  have hconjCent : conjSub w (Z ⊔ M6 c.e) ≤ Subgroup.centralizer (V1 c.e : Set G) := by
    intro x hx
    rw [conjSub, Subgroup.mem_map] at hx
    obtain ⟨q, hq, rfl⟩ := hx
    simpa [MulAut.conj_apply] using hW_cent_conj w hwW q (hQ_le_cent hq)
  have hconjM6 : conjSub w (Z ⊔ M6 c.e) ≤ M6 c.e := le_inf hconjC6 hconjCent
  have hcard_eq : Nat.card ((Z ⊔ M6 c.e).map (MulAut.conj w).toMonoidHom) =
      Nat.card ↥(Z ⊔ M6 c.e) :=
    Subgroup.card_map_of_injective (MulAut.conj w).injective
  have hcard : Nat.card ↥(Z ⊔ M6 c.e) ≤ Nat.card ↥(M6 c.e) := by
    rw [← hcard_eq]
    exact Subgroup.card_le_of_le
      (show (Z ⊔ M6 c.e).map (MulAut.conj w).toMonoidHom ≤ M6 c.e from hconjM6)
  have heq : M6 c.e = Z ⊔ M6 c.e := Subgroup.eq_of_le_of_card_ge le_sup_right hcard
  intro z hz
  rw [heq]
  exact (le_sup_left : Z ≤ Z ⊔ M6 c.e) hz

theorem y7n_cent_P1_K {c : Ctx7 G L} (h7 : c.Upto79) {L1 : Subgroup G}
    (hL1 : IsCompPre c.s L1)
    (hLam : ∀ x ∈ ⁅L1, L1⁆, (∀ y ∈ ⁅L1, L1⁆, y * x = x * y) → x = 1)
    {P1 : Subgroup G} (hP1 : IsPGroup 2 P1) {z : G} (hz : z ∈ P1)
    (hzL : ∀ x ∈ ⁅L1, L1⁆, z * x = x * z)
    (hzLt : ∀ y ∈ conjSub c.s.t ⁅L1, L1⁆, z * y = y * z) : z = 1 := by
  have h7keep := h7
  obtain ⟨⟨⟨⟨⟨⟨⟨⟨_h71, _h72⟩, _h73⟩, _h74⟩, _h75⟩, _h76⟩, h77⟩, _h78⟩, h79⟩ := h7
  have hdir : IsInternalDirect (K7 c.s) ⁅L1, L1⁆ (conjSub c.s.t ⁅L1, L1⁆) := (h79 L1 hL1).1
  have hKeq : ⁅L1, L1⁆ ⊔ conjSub c.s.t ⁅L1, L1⁆ = K7 c.s := hdir.1
  have hcomm : ∀ u ∈ ⁅L1, L1⁆, ∀ v ∈ conjSub c.s.t ⁅L1, L1⁆, u * v = v * u := hdir.2.2
  have hM6_le_K : M6 c.e ≤ K7 c.s :=
    (show M6 c.e ≤ P7 c.e from le_sup_left).trans h77.1.1
  have hzK_cent : K7 c.s ≤ Subgroup.centralizer ({z} : Set G) := by
    rw [← hKeq]
    exact sup_le
      (fun x hx => Subgroup.mem_centralizer_singleton_iff.mpr (hzL x hx).symm)
      (fun y hy => Subgroup.mem_centralizer_singleton_iff.mpr (hzLt y hy).symm)
  have hzM6 : ∀ m ∈ M6 c.e, z * m = m * z := fun m hm =>
    (Subgroup.mem_centralizer_singleton_iff.mp (hzK_cent (hM6_le_K hm))).symm
  have hzcentM6 : z ∈ Subgroup.centralizer (M6 c.e : Set G) :=
    Subgroup.mem_centralizer_iff.mpr fun m hm => (hzM6 m hm).symm
  have hZc : ∀ z' ∈ Subgroup.zpowers z, ∀ m ∈ M6 c.e, z' * m = m * z' := by
    intro z' hz' m hm
    exact (Subgroup.mem_centralizer_iff.mp (Subgroup.zpowers_le.mpr hzcentM6 hz') m hm).symm
  have hZp : IsPGroup 2 (Subgroup.zpowers z) := hP1.to_le (Subgroup.zpowers_le.mpr hz)
  have hzM6mem : z ∈ M6 c.e := y7n_cent_two_le_M6 h7keep hZp hZc (Subgroup.mem_zpowers z)
  have hzK : z ∈ K7 c.s := hM6_le_K hzM6mem
  have hLam_t_cent : conjSub c.s.t ⁅L1, L1⁆ ≤
      Subgroup.centralizer ((⁅L1, L1⁆ : Subgroup G) : Set G) :=
    fun v hv => Subgroup.mem_centralizer_iff.mpr (fun u hu => hcomm u hu v hv)
  have hLam_t_norm : conjSub c.s.t ⁅L1, L1⁆ ≤
      Subgroup.normalizer ((⁅L1, L1⁆ : Subgroup G) : Set G) :=
    hLam_t_cent.trans
      (Subgroup.centralizer_le_normalizer ((⁅L1, L1⁆ : Subgroup G) : Set G))
  have hdecomp : (↑(K7 c.s) : Set G) =
      ((⁅L1, L1⁆ : Subgroup G) : Set G) * (conjSub c.s.t ⁅L1, L1⁆ : Set G) := by
    rw [← hKeq]
    exact Subgroup.coe_mul_of_right_le_normalizer_left _ _ hLam_t_norm
  have hzK' : z ∈ (K7 c.s : Set G) := hzK
  rw [hdecomp] at hzK'
  obtain ⟨a, ha, b, hb, hab⟩ := hzK'
  have ha_cent : ∀ y ∈ ⁅L1, L1⁆, y * a = a * y := by
    intro y hy
    have hbz : a = z * b⁻¹ := by rw [← hab]; group
    have hby : y * b⁻¹ = b⁻¹ * y :=
      (Commute.inv_right (show Commute y b from hcomm y hy b hb)).eq
    calc y * a = y * (z * b⁻¹) := by rw [hbz]
      _ = (y * z) * b⁻¹ := by group
      _ = (z * y) * b⁻¹ := by rw [hzL y hy]
      _ = z * (y * b⁻¹) := by group
      _ = z * (b⁻¹ * y) := by rw [hby]
      _ = (z * b⁻¹) * y := by group
      _ = a * y := by rw [hbz]
  have ha1 : a = 1 := hLam a ha ha_cent
  have hb_eq_z : b = z := by
    have h := hab
    simp only [ha1, one_mul] at h
    exact h
  have hb_cent : ∀ w ∈ conjSub c.s.t ⁅L1, L1⁆, w * b = b * w := by
    intro w hw
    rw [hb_eq_z]
    exact (hzLt w hw).symm
  have hb'_mem : c.s.t⁻¹ * b * c.s.t ∈ ⁅L1, L1⁆ := by
    obtain ⟨d, hd, hdb⟩ := hb
    simp only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply] at hdb
    have hd_eq : d = c.s.t⁻¹ * b * c.s.t := by rw [← hdb]; group
    rw [← hd_eq]
    exact hd
  have hb'_cent : ∀ u ∈ ⁅L1, L1⁆,
      u * (c.s.t⁻¹ * b * c.s.t) = (c.s.t⁻¹ * b * c.s.t) * u := by
    intro u hu
    have htu : c.s.t * u * c.s.t⁻¹ ∈ conjSub c.s.t ⁅L1, L1⁆ := by
      rw [conjSub, Subgroup.mem_map]
      exact ⟨u, hu, by simp [MulAut.conj_apply]⟩
    have hbu := hb_cent (c.s.t * u * c.s.t⁻¹) htu
    calc u * (c.s.t⁻¹ * b * c.s.t) =
        c.s.t⁻¹ * ((c.s.t * u * c.s.t⁻¹) * b) * c.s.t := by group
      _ = c.s.t⁻¹ * (b * (c.s.t * u * c.s.t⁻¹)) * c.s.t := by rw [hbu]
      _ = (c.s.t⁻¹ * b * c.s.t) * u := by group
  have hb'1 : c.s.t⁻¹ * b * c.s.t = 1 := hLam _ hb'_mem hb'_cent
  have hb1 : b = 1 := by
    calc b = c.s.t * (c.s.t⁻¹ * b * c.s.t) * c.s.t⁻¹ := by group
      _ = c.s.t * 1 * c.s.t⁻¹ := by rw [hb'1]
      _ = 1 := by group
  have hz1 : z = 1 := by
    have h := hab
    simp only [ha1, hb1, one_mul] at h
    exact h.symm
  exact hz1

end CFSG.OddStandard.HigherRank.YamadaG23
