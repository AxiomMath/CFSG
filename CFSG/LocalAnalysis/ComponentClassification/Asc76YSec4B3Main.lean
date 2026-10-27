module

public import CFSG.LocalAnalysis.ComponentClassification.Asc76YSec4B3Gen

public section

namespace CFSG.ComponentClassification.Asc76.Sec4

open Subgroup CFSG.ABGLocalTools CFSG.ComponentClassification.AschbacherTightEmbedding
  CFSG.ComponentClassification.AS76b

variable {G : Type} [Group G] [Finite G] {Ω : Set (Subgroup G)} {S : Subgroup G}

omit [Finite G] in
theorem DSet.le_mGrp {W T : Subgroup G} (hT : T ∈ DSet Ω W) : T ≤ MGrp Ω W :=
  le_iSup₂_of_le (f := fun T (_ : T ∈ DSet Ω W) => T) T hT le_rfl

omit [Finite G] in
theorem MGrp.le_normalizer {W : Subgroup G} : MGrp Ω W ≤ normalizer (W : Set G) :=
  iSup_le fun _ => iSup_le fun hT => by
    obtain ⟨-, h⟩ := hT
    exact h

omit [Finite G] in
theorem MBar.exists_mGrp {W : Subgroup G} {c : NBar W} (hc : c ∈ MBar Ω W) :
    ∃ n : normalizer (W : Set G), (n : G) ∈ MGrp Ω W ∧ (n : NBar W) = c := by
  have hle : MBar Ω W ≤ ((MGrp Ω W).subgroupOf (normalizer (W : Set G))).map
      (QuotientGroup.mk' (cInN W)) := by
    rw [closure_le]
    rintro d ⟨J, hJ, T, V, hTJ, hV, hTW, t, htT, htV, rfl⟩
    exact ⟨t, mem_subgroupOf.mpr (DSet.le_mGrp ⟨⟨J, hJ, hTJ⟩, hTW⟩ htT), rfl⟩
  obtain ⟨n, hn, hnc⟩ := hle hc
  exact ⟨n, mem_subgroupOf.mp hn, hnc⟩

theorem DSet.exists_mGrp_conj (H : Sec4Hyp Ω) (hS : IsSylowOf 2 S ⊤)
    (hdis : ¬ (CFSG.Fischer.commGraph (DBar Ω (sec4W Ω S))).Connected)
    {T₁ T₂ : Subgroup G} (hT₁ : T₁ ∈ DSet Ω (sec4W Ω S)) (hT₂ : T₂ ∈ DSet Ω (sec4W Ω S)) :
    ∃ m ∈ MGrp Ω (sec4W Ω S), T₂ = AschbacherTightEmbedding.rightConjugate T₁ m := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hΩne : Ω.Nonempty := by
    obtain ⟨⟨J, hJ, -⟩, -⟩ := hT₁
    exact ⟨J, hJ⟩
  obtain ⟨d₁, hd₁⟩ := IsBarOf.exists_of_mem H.hΩ hT₁
  obtain ⟨d₂, hd₂⟩ := IsBarOf.exists_of_mem H.hΩ hT₂
  have hd₁D := IsBarOf.mem_dBar hT₁ hd₁
  have hd₂D := IsBarOf.mem_dBar hT₂ hd₂
  obtain ⟨φ, -, -, -, -, hconj⟩ := DBar.exists_hom_perm_three H hS hΩne hdis
  obtain ⟨c, hc⟩ := isConj_iff.mp (hconj ⟨d₁, subset_closure hd₁D⟩ ⟨d₂, subset_closure hd₂D⟩
    hd₁D hd₂D)
  have hc' : (c : NBar (sec4W Ω S)) * d₁ * (c : NBar (sec4W Ω S))⁻¹ = d₂ := by
    simpa using congrArg Subtype.val hc
  obtain ⟨n, hnM, hn⟩ := MBar.exists_mGrp (inv_mem c.2)
  have hT₁M := DSet.le_mGrp hT₁
  have hT₂M := DSet.le_mGrp hT₂
  have hT₁n : AschbacherTightEmbedding.rightConjugate T₁ (n : G) ∈ DSet Ω (sec4W Ω S) :=
    DSet.rightConjugate_mem H.hΩ hT₁ n.2
  have hbar := hd₁.rightConjugate n
  rw [hn, inv_inv, hc'] at hbar
  obtain ⟨⟨J₁, hJ₁, h₁⟩, -⟩ := hT₁
  obtain ⟨⟨J₂, hJ₂, h₂⟩, hT₂W⟩ := hT₂
  have hJ₁n := H.hΩ.conj_mem J₁ hJ₁ n
  have h₁n := isSylowOf_rightConjugate h₁ (n : G)
  obtain ⟨-, hT₁nW⟩ := hT₁n
  have hJJ := member_eq_of_bar_eq H hS hJ₁n hJ₂ h₁n h₂ hT₁nW hT₂W hbar hd₂
  rw [hJJ] at h₁n
  have hT₁nM : AschbacherTightEmbedding.rightConjugate T₁ (n : G) ≤ MGrp Ω (sec4W Ω S) := by
    intro x hx
    rw [mem_rightConjugate_iff] at hx
    have e : x = (n : G)⁻¹ * ((n : G) * x * (n : G)⁻¹) * n := by group
    rw [e]
    exact mul_mem (mul_mem (inv_mem hnM) (hT₁M hx)) hnM
  have hP : IsSylowOf 2 (AschbacherTightEmbedding.rightConjugate T₁ (n : G))
      (J₂ ⊓ MGrp Ω (sec4W Ω S)) := h₁n.of_le (le_inf h₁n.le hT₁nM) inf_le_left
  have hP' : IsSylowOf 2 T₂ (J₂ ⊓ MGrp Ω (sec4W Ω S)) := h₂.of_le (le_inf h₂.le hT₂M) inf_le_left
  obtain ⟨k, hk, hkx⟩ := CFSG.ComponentClassification.Asc76.L26.IsSylowOf.exists_conj_mem hP hP'
  refine ⟨(n : G) * k⁻¹, mul_mem hnM (inv_mem (mem_inf.mp hk).2), ?_⟩
  ext x
  rw [hkx x, mem_rightConjugate_iff, mem_rightConjugate_iff]
  constructor
  · intro h
    have e : (n : G) * k⁻¹ * x * ((n : G) * k⁻¹)⁻¹ =
        (n : G) * (k⁻¹ * x * k) * (n : G)⁻¹ := by group
    rw [e]
    exact h
  · intro h
    have e : (n : G) * k⁻¹ * x * ((n : G) * k⁻¹)⁻¹ =
        (n : G) * (k⁻¹ * x * k) * (n : G)⁻¹ := by group
    rw [e] at h
    exact h

theorem DSet.mem_conj_zOf (H : Sec4Hyp Ω) (hS : IsSylowOf 2 S ⊤)
    (hdis : ¬ (CFSG.Fischer.commGraph (DBar Ω (sec4W Ω S))).Connected)
    {R T : Subgroup G} (hR : R ∈ DSet Ω (sec4W Ω S)) (hT : T ∈ DSet Ω (sec4W Ω S)) {z y : G}
    (hz : IsZOf R z) (hy : IsZOf T y) : ∃ m ∈ MGrp Ω (sec4W Ω S), y = m⁻¹ * z * m := by
  obtain ⟨m, hm, rfl⟩ := DSet.exists_mGrp_conj H hS hdis hR hT
  exact ⟨m, hm, hy.unique (hz.rightConjugate m)⟩

theorem DSet.step_zOf (H : Sec4Hyp Ω) (hS : IsSylowOf 2 S ⊤) (hΩne : Ω.Nonempty)
    (hdis : ¬ (CFSG.Fischer.commGraph (DBar Ω (sec4W Ω S))).Connected)
    {r f g : NBar (sec4W Ω S)} (hr : r ∈ DBar Ω (sec4W Ω S)) {T Tg Vg : Subgroup G}
    {tg : normalizer (sec4W Ω S : Set G)} {y zg : G} (hT : T ∈ DSet Ω (sec4W Ω S))
    (hf : IsBarOf (sec4W Ω S) T f) (hy : IsZOf T y) (hfr : f * r ≠ r * f)
    (hg : ReflData Ω (sec4W Ω S) g Tg Vg tg) (hgr : g * r = r * g) (hzg : IsZOf Tg zg) :
    AschbacherTightEmbedding.rightConjugate T (tg : G) ∈ DSet Ω (sec4W Ω S) ∧
      IsBarOf (sec4W Ω S) (AschbacherTightEmbedding.rightConjugate T (tg : G)) (g * f * g) ∧
      IsZOf (AschbacherTightEmbedding.rightConjugate T (tg : G)) (y * zg) ∧
      (g * f * g) * r ≠ r * (g * f * g) := by
  have hgD := hg.mem_dBar
  have hfD := IsBarOf.mem_dBar hT hf
  have hginv : g⁻¹ = g := inv_eq_of_mul_eq_one_right (DBar.mul_self H.hΩ hS hgD)
  have hgf : g * f ≠ f * g := fun h =>
    hfr (DBar.commute_trans H hS hΩne hdis hfD hgD hr h.symm hgr)
  refine ⟨DSet.rightConjugate_mem H.hΩ hT tg.2, ?_, ?_, ?_⟩
  · have h1 := hf.rightConjugate tg
    rwa [hg.eq, hginv] at h1
  · have h1 := hy.rightConjugate (tg : G)
    rwa [conj_z_of_not_commute H hS hg.mem hT hg.rot hzg hy hg.bar hf hgf hg.memT hg.not_mem]
      at h1
  · intro h
    apply hgf
    have h1 : (g * f * g) * g = g * (g * f * g) :=
      DBar.commute_trans H hS hΩne hdis (DBar.conj_mem' H.hΩ hS hfD hgD) hr hgD h hgr.symm
    have hgg := DBar.mul_self H.hΩ hS hgD
    have e1 : (g * f * g) * g = g * f := by rw [mul_assoc, hgg, mul_one]
    have e2 : g * (g * f * g) = f * g := by rw [← mul_assoc, ← mul_assoc, hgg, one_mul]
    rw [e1, e2] at h1
    exact h1

omit [Finite G] in
theorem mul_mem_zZero {W R T : Subgroup G} {z y : G} (hT : T ∈ DSet Ω W) (hy : IsZOf T y)
    (hc : ∀ r s : NBar W, IsBarOf W R r → IsBarOf W T s → r * s = s * r) :
    z * y ∈ zZero Ω W R z := ⟨T, hT, y, hy, hc, rfl⟩

theorem mul_mem_zZero_of_bar (hΩ : Assumption41 Ω) (hS : IsSylowOf 2 S ⊤) {R T : Subgroup G}
    (hR : R ∈ DSet Ω (sec4W Ω S)) (hT : T ∈ DSet Ω (sec4W Ω S)) {r s : NBar (sec4W Ω S)}
    (hr : IsBarOf (sec4W Ω S) R r) (hs : IsBarOf (sec4W Ω S) T s) (hsr : s * r = r * s)
    {z y : G} (hy : IsZOf T y) : z * y ∈ zZero Ω (sec4W Ω S) R z :=
  mul_mem_zZero hT hy fun r' s' hr' hs' => by
    rw [← IsBarOf.unique hΩ hS hR hr hr', ← IsBarOf.unique hΩ hS hT hs hs']
    exact hsr.symm

theorem DSet.commute_zOf_of_commute (H : Sec4Hyp Ω) (hS : IsSylowOf 2 S ⊤)
    {T₁ T₂ : Subgroup G} (hT₁ : T₁ ∈ DSet Ω (sec4W Ω S)) (hT₂ : T₂ ∈ DSet Ω (sec4W Ω S))
    {z₂ : G} (hz₂ : IsZOf T₂ z₂) {d₁ d₂ : NBar (sec4W Ω S)} (hd₁ : IsBarOf (sec4W Ω S) T₁ d₁)
    (hd₂ : IsBarOf (sec4W Ω S) T₂ d₂) (hc : d₁ * d₂ = d₂ * d₁) {x : G} (hx : x ∈ T₁) :
    x * z₂ = z₂ * x := by
  by_cases hne : d₁ = d₂
  · subst hne
    obtain ⟨V₁, hV₁⟩ := DSet.exists_rot H.hΩ hT₁
    obtain ⟨z₁, hz₁⟩ := IsZOf.exists_of_rot hV₁
    rw [← DSet.zOf_eq_of_bar_eq H hS hT₁ hT₂ hz₁ hz₂ hd₁ hd₂]
    exact hz₁.commute hx
  · exact commute_z_of_commute H hS hT₁ hT₂ hz₂ hd₁ hd₂ hc hne hx

theorem DSet.zOf_mem (hΩ : Assumption41 Ω) (hS : IsSylowOf 2 S ⊤) {T : Subgroup G}
    (hT : T ∈ DSet Ω (sec4W Ω S)) {y : G} (hy : IsZOf T y) : y ∈ sec4W Ω S := by
  obtain ⟨V, hV⟩ := DSet.exists_rot hΩ hT
  exact DSet.rot_le hΩ hS hT hV (hy.mem_rot hV).1

theorem zZero_commute (H : Sec4Hyp Ω) (hS : IsSylowOf 2 S ⊤)
    (hdis : ¬ (CFSG.Fischer.commGraph (DBar Ω (sec4W Ω S))).Connected)
    {R : Subgroup G} (hR : R ∈ DSet Ω (sec4W Ω S)) {z : G} (hz : IsZOf R z) {x : G}
    (hx : x ∈ zZero Ω (sec4W Ω S) R z) {m : G} (hm : m ∈ MGrp Ω (sec4W Ω S)) :
    m * x = x * m := by
  have hΩ := H.hΩ
  have hΩne : Ω.Nonempty := by
    obtain ⟨⟨J, hJ, -⟩, -⟩ := hR
    exact ⟨J, hJ⟩
  obtain ⟨T, hT, y, hy, hc, rfl⟩ := hx
  obtain ⟨r, hr⟩ := IsBarOf.exists_of_mem hΩ hR
  obtain ⟨s, hs⟩ := IsBarOf.exists_of_mem hΩ hT
  have hrs := hc r s hr hs
  have hrD := IsBarOf.mem_dBar hR hr
  have hsD := IsBarOf.mem_dBar hT hs
  have hzW := DSet.zOf_mem hΩ hS hR hz
  have hyW := DSet.zOf_mem hΩ hS hT hy
  have hle : MGrp Ω (sec4W Ω S) ≤ centralizer ({z * y} : Set G) := by
    refine iSup_le fun Q => iSup_le fun hQ => ?_
    intro q hq
    rw [mem_centralizer_singleton_iff]
    obtain ⟨e, he⟩ := IsBarOf.exists_of_mem hΩ hQ
    have heD := IsBarOf.mem_dBar hQ he
    by_cases her : e * r = r * e
    · have hes : e * s = s * e := DBar.commute_trans H hS hΩne hdis heD hrD hsD her hrs
      have h1 := DSet.commute_zOf_of_commute H hS hQ hR hz he hr her hq
      have h2 := DSet.commute_zOf_of_commute H hS hQ hT hy he hs hes hq
      calc q * (z * y) = z * (q * y) := by rw [← mul_assoc, h1, mul_assoc]
        _ = z * y * q := by rw [h2, mul_assoc]
    · obtain ⟨VQ, hVQ⟩ := DSet.exists_rot hΩ hQ
      by_cases hqV : q ∈ VQ
      · exact sec4W_comm hΩ hS (DSet.rot_le hΩ hS hQ hVQ hqV) (mul_mem hzW hyW)
      · obtain ⟨zQ, hzQ⟩ := IsZOf.exists_of_rot hVQ
        have hes : e * s ≠ s * e := fun h =>
          her (DBar.commute_trans H hS hΩne hdis heD hsD hrD h hrs.symm)
        have h1 : q⁻¹ * z * q = z * zQ :=
          conj_z_of_not_commute H hS hQ hR hVQ hzQ hz he hr her hq hqV
        have h2 : q⁻¹ * y * q = y * zQ :=
          conj_z_of_not_commute H hS hQ hT hVQ hzQ hy he hs hes hq hqV
        have hzQW := DSet.zOf_mem hΩ hS hQ hzQ
        have h3 : q⁻¹ * (z * y) * q = z * y := by
          calc q⁻¹ * (z * y) * q = (q⁻¹ * z * q) * (q⁻¹ * y * q) := by group
            _ = z * (zQ * y) * zQ := by rw [h1, h2]; group
            _ = z * (y * zQ) * zQ := by rw [sec4W_comm hΩ hS hzQW hyW]
            _ = z * y * (zQ * zQ) := by group
            _ = z * y := by rw [hzQ.mul_self, mul_one]
        calc q * (z * y) = q * (q⁻¹ * (z * y) * q) := by rw [h3]
          _ = z * y * q := by group
  exact mem_centralizer_singleton_iff.mp (hle hm)

theorem conj_mem_omegaOne_diff (H : Sec4Hyp Ω) (hS : IsSylowOf 2 S ⊤)
    (hdis : ¬ (CFSG.Fischer.commGraph (DBar Ω (sec4W Ω S))).Connected)
    {R : Subgroup G} (hR : R ∈ DSet Ω (sec4W Ω S)) {z : G} (hz : IsZOf R z) {m : G}
    (hm : m ∈ MGrp Ω (sec4W Ω S)) :
    m⁻¹ * z * m ∈ omegaOne (sec4W Ω S) \ zZero Ω (sec4W Ω S) R z := by
  have hΩ := H.hΩ
  have hmN : m ∈ normalizer (sec4W Ω S : Set G) := MGrp.le_normalizer hm
  have hzW := DSet.zOf_mem hΩ hS hR hz
  refine ⟨⟨conj_mem_sec4W hmN hzW, ?_⟩, ?_⟩
  · rw [show m⁻¹ * z * m * (m⁻¹ * z * m) = m⁻¹ * (z * z) * m by group, hz.mul_self]
    group
  intro h0
  have hRm := DSet.rightConjugate_mem hΩ hR hmN
  have hzm := hz.rightConjugate m
  obtain ⟨e, he⟩ := IsBarOf.exists_of_mem hΩ hRm
  obtain ⟨f, hfD, hef⟩ := DBar.exists_not_commute hdis (IsBarOf.mem_dBar hRm he)
  obtain ⟨Tf, Vf, tf, htf⟩ := DBar.exists_reflData hfD
  obtain ⟨zf, hzf⟩ := IsZOf.exists_of_rot htf.rot
  have h1 := conj_z_of_not_commute H hS htf.mem hRm htf.rot hzf hzm htf.bar he
    (fun h => hef h.symm) htf.memT htf.not_mem
  have h2 := zZero_commute H hS hdis hR hz h0 (DSet.le_mGrp htf.mem htf.memT)
  have h3 : (tf : G)⁻¹ * (m⁻¹ * z * m) * tf = m⁻¹ * z * m := by
    calc (tf : G)⁻¹ * (m⁻¹ * z * m) * tf = (tf : G)⁻¹ * ((m⁻¹ * z * m) * tf) := by group
      _ = (tf : G)⁻¹ * (tf * (m⁻¹ * z * m)) := by rw [← h2]
      _ = m⁻¹ * z * m := by group
  rw [h1] at h3
  apply hzf.ne_one
  calc zf = (m⁻¹ * z * m)⁻¹ * ((m⁻¹ * z * m) * zf) := by group
    _ = 1 := by rw [h3, inv_mul_cancel]

end CFSG.ComponentClassification.Asc76.Sec4
