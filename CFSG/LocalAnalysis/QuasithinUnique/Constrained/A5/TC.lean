module

public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.A5.SylowS

public section

namespace CFSG.QuasithinUnique.A5

open CFSG.Open CFSG.Quasithin CFSG.QuasithinUnique CFSG.QuasithinUnique.DoubleA3
  CFSG.QuasithinUnique.A5.Delta5

namespace StdCfg

variable {G : Type} [Group G] [Finite G] {T M H S L : Subgroup G}

theorem exists_mem_T_sdiff (C : StdCfg T M H S L) : ∃ x ∈ T, x ∉ S := by
  by_contra hcon
  push Not at hcon
  exact C.hcs.ne_T (le_antisymm C.hcs.le_T hcon)

theorem T_le_normalizer_S (C : StdCfg T M H S L) : T ≤ Subgroup.normalizer (S : Set G) :=
  normalizer_of_relIndex_two C.hcs.le_T C.F.index_two

theorem TC_le_Q (C : StdCfg T M H S L) : blockTC T S L ≤ pCoreOf 2 H := by
  rw [C.F.Q_eq]; exact le_sup_left

theorem TC_le_S (C : StdCfg T M H S L) : blockTC T S L ≤ S := C.TC_le_Q.trans C.pCoreOf_le_S

theorem TC_comm_TC (C : StdCfg T M H S L) {a b : G} (ha : a ∈ blockTC T S L)
    (hb : b ∈ blockTC T S L) : a * b = b * a :=
  (C5.isElemAbelian_two_iff.mp C.F.TC_abel).1 a ha b hb

theorem TC_sq (C : StdCfg T M H S L) {a : G} (ha : a ∈ blockTC T S L) : a ^ 2 = 1 :=
  (C5.isElemAbelian_two_iff.mp C.F.TC_abel).2 a ha

theorem TC_comm_L (C : StdCfg T M H S L) {t l : G} (ht : t ∈ blockTC T S L) (hl : l ∈ L) :
    t * l = l * t := by
  have h : t ∈ Subgroup.centralizer (conjJoin S L : Set G) := ht.2
  rw [C.hj] at h
  exact (Subgroup.mem_centralizer_iff.mp h l hl).symm

theorem TC_comm_R (C : StdCfg T M H S L) {t r : G} (ht : t ∈ blockTC T S L)
    (hr : r ∈ baum S) : t * r = r * t := by
  obtain ⟨x, hxT, hxS⟩ := C.exists_mem_T_sdiff
  have hle : baum S ≤ Subgroup.centralizer ({t} : Set G) := by
    rw [C.F.R_eq x hxT hxS]
    refine sup_le ?_ (sup_le ?_ ?_)
    · intro a ha
      rw [Subgroup.mem_centralizer_iff]
      intro h hh
      rw [Set.mem_singleton_iff] at hh
      rw [hh]
      exact C.TC_comm_TC ht ha
    · intro y hy
      rw [Subgroup.mem_centralizer_iff]
      intro h hh
      rw [Set.mem_singleton_iff] at hh
      rw [hh]
      exact C.F.TC_comm x hxT hxS t ht y (Subgroup.mem_sup_left hy)
    · intro y hy
      rw [Subgroup.mem_centralizer_iff]
      intro h hh
      rw [Set.mem_singleton_iff] at hh
      rw [hh]
      exact C.F.TC_comm x hxT hxS t ht y (Subgroup.mem_sup_right hy)
  exact Subgroup.mem_centralizer_iff.mp (hle hr) t (Set.mem_singleton t)

theorem TC_comm_H (C : StdCfg T M H S L) {t h : G} (ht : t ∈ blockTC T S L) (hh : h ∈ H) :
    t * h = h * t := by
  have hle : H ≤ Subgroup.centralizer ({t} : Set G) := by
    rw [C.hHeq]
    refine sup_le ?_ ?_
    · intro l hl
      rw [Subgroup.mem_centralizer_iff]
      intro h' hh'
      rw [Set.mem_singleton_iff] at hh'
      rw [hh']
      exact C.TC_comm_L ht hl
    · intro r hr
      rw [Subgroup.mem_centralizer_iff]
      intro h' hh'
      rw [Set.mem_singleton_iff] at hh'
      rw [hh']
      exact C.TC_comm_R ht hr
  exact Subgroup.mem_centralizer_iff.mp (hle hh) t (Set.mem_singleton t)

theorem conj_TC_cent_S (C : StdCfg T M H S L) {x : G} (hxT : x ∈ T) {a : G}
    (ha : a ∈ blockTC T S L) : ∀ s ∈ S, s * (x⁻¹ * a * x) * s⁻¹ = x⁻¹ * a * x := by
  intro s hs
  have hxn' : x ∈ Subgroup.normalizer (S : Set G) := C.T_le_normalizer_S hxT
  have hs' : x * s * x⁻¹ ∈ S := (Subgroup.mem_normalizer_iff.mp hxn' s).mp hs
  have hcomm : a * (x * s * x⁻¹) = (x * s * x⁻¹) * a := C.TC_comm_H ha (C.hcs.sylow.le hs')
  calc s * (x⁻¹ * a * x) * s⁻¹
      = x⁻¹ * ((x * s * x⁻¹) * a * (x * s * x⁻¹)⁻¹) * x := by group
    _ = x⁻¹ * a * x := by rw [← hcomm]; group

theorem conj_TC_mem_Q (C : StdCfg T M H S L) {x : G} (hxT : x ∈ T) {a : G}
    (ha : a ∈ blockTC T S L) : x⁻¹ * a * x ∈ pCoreOf 2 H := by
  have hxn : x⁻¹ ∈ Subgroup.normalizer (S : Set G) := inv_mem (C.T_le_normalizer_S hxT)
  have hyS : x⁻¹ * a * x ∈ S := by
    have := (Subgroup.mem_normalizer_iff.mp hxn a).mp (C.TC_le_S ha)
    simpa using this
  have hcU : x⁻¹ * a * x ∈ Subgroup.centralizer (blockU L : Set G) := by
    rw [Subgroup.mem_centralizer_iff]
    intro u hu
    have := C.conj_TC_cent_S hxT ha u (blockU_le_S C.hcs C.hj hu)
    calc u * (x⁻¹ * a * x) = (u * (x⁻¹ * a * x) * u⁻¹) * u := by group
      _ = (x⁻¹ * a * x) * u := by rw [this]
  rw [← C56.inf_centralizer_eq C.hcs C.hj]
  exact ⟨C.hcs.sylow.le hyS, hcU⟩

theorem conj_TC_decomp (C : StdCfg T M H S L) {x : G} (hxT : x ∈ T) {a : G}
    (ha : a ∈ blockTC T S L) :
    ∃ t₁ ∈ blockTC T S L, x⁻¹ * a * x = t₁ ∨ x⁻¹ * a * x = t₁ * C.zU := by
  have hy := C.conj_TC_mem_Q hxT ha
  rw [C.F.Q_eq] at hy
  have hcomm : ∀ a ∈ blockTC T S L, ∀ b ∈ blockU L, a * b = b * a := fun a ha b hb =>
    C.TC_comm_L ha (blockU_le_L C.hcs hb)
  obtain ⟨t₁, ht₁, u₁, hu₁, hy'⟩ := C5.mem_sup_of_commute hcomm hy
  refine ⟨t₁, ht₁, ?_⟩
  have hu₁S : ∀ s ∈ S, s * u₁ * s⁻¹ = u₁ := by
    intro s hs
    have h1 : u₁ = t₁⁻¹ * (x⁻¹ * a * x) := by rw [hy']; group
    have h2 : s * t₁ * s⁻¹ = t₁ := by
      have := C.TC_comm_H ht₁ (C.hcs.sylow.le hs)
      calc s * t₁ * s⁻¹ = (t₁ * s) * s⁻¹ := by rw [← this]
        _ = t₁ := by group
    have h3 := C.conj_TC_cent_S hxT ha s hs
    calc s * u₁ * s⁻¹ = (s * t₁ * s⁻¹)⁻¹ * (s * (x⁻¹ * a * x) * s⁻¹) := by rw [h1]; group
      _ = t₁⁻¹ * (x⁻¹ * a * x) := by rw [h2, h3]
      _ = u₁ := h1.symm
  rcases C.CU_S hu₁ hu₁S with h | h
  · left; rw [hy', h, mul_one]
  · right; rw [hy', h]

theorem eq_one_of_conj_mem_TC (C : StdCfg T M H S L) {x : G} (hxT : x ∈ T) (hxS : x ∉ S)
    {a : G} (ha : a ∈ blockTC T S L) (h : x⁻¹ * a * x ∈ blockTC T S L) : a = 1 := by
  have hmem : x⁻¹ * a * x ∈ blockTC T S L ⊓ conjR (blockTC T S L) x := by
    refine ⟨h, ?_⟩
    show x⁻¹ * a * x ∈ conjSubgroup (blockTC T S L) x
    rw [mem_conjSubgroup_iff, show x * (x⁻¹ * a * x) * x⁻¹ = a by group]
    exact ha
  rw [C.F.TC_inf_conj x hxT hxS] at hmem
  have h1 : x⁻¹ * a * x = 1 := hmem
  calc a = x * (x⁻¹ * a * x) * x⁻¹ := by group
    _ = 1 := by rw [h1]; group

theorem eq_one_of_conj_eq_zU (C : StdCfg T M H S L) {x : G} (hxT : x ∈ T) (hxS : x ∉ S)
    {a : G} (ha : a ∈ blockTC T S L) (h : x⁻¹ * a * x = C.zU) : a = 1 := by
  have hxT' : x⁻¹ ∈ T := inv_mem hxT
  have hxS' : x⁻¹ ∉ S := fun h' => hxS (by simpa using inv_mem h')
  have hmem : a ∈ blockTC T S L ⊓ (blockU L ⊔ conjR (blockU L) x⁻¹) := by
    refine ⟨ha, Subgroup.mem_sup_right ?_⟩
    show a ∈ conjSubgroup (blockU L) x⁻¹
    rw [mem_conjSubgroup_iff, inv_inv, h]
    exact C.zU_mem
  rw [C.F.TC_inf_UU x⁻¹ hxT' hxS'] at hmem
  exact hmem

theorem TC_conj_form (C : StdCfg T M H S L) {x : G} (hxT : x ∈ T) (hxS : x ∉ S) {a : G}
    (ha : a ∈ blockTC T S L) (ha1 : a ≠ 1) :
    ∃ t₁ ∈ blockTC T S L, t₁ ≠ 1 ∧ x⁻¹ * a * x = t₁ * C.zU := by
  obtain ⟨t₁, ht₁, h | h⟩ := C.conj_TC_decomp hxT ha
  · exact absurd (C.eq_one_of_conj_mem_TC hxT hxS ha (h ▸ ht₁)) ha1
  · refine ⟨t₁, ht₁, ?_, h⟩
    rintro rfl
    rw [one_mul] at h
    exact ha1 (C.eq_one_of_conj_eq_zU hxT hxS ha h)

theorem TC_structure (C : StdCfg T M H S L) (hne : blockTC T S L ≠ ⊥) :
    ∃ t ∈ blockTC T S L, t ≠ 1 ∧ (∀ a ∈ blockTC T S L, a = 1 ∨ a = t) ∧
      ∀ x ∈ T, x ∉ S → x⁻¹ * t * x = t * C.zU := by
  obtain ⟨x₀, hx₀T, hx₀S⟩ := C.exists_mem_T_sdiff
  obtain ⟨t, ht1⟩ := (Subgroup.ne_bot_iff_exists_ne_one).mp hne
  have ht : (t : G) ∈ blockTC T S L := t.2
  have htne : (t : G) ≠ 1 := fun h => ht1 (Subtype.ext h)
  have hsmall : ∀ a ∈ blockTC T S L, a ≠ 1 → a = t := by
    intro a ha ha1
    by_contra hat
    have hat1 : a * t ≠ 1 := by
      intro h
      apply hat
      have h2 : a = (t : G)⁻¹ := eq_inv_of_mul_eq_one_left h
      have h3 : (t : G)⁻¹ = t := by
        have := C.TC_sq ht
        rw [pow_two] at this
        exact inv_eq_of_mul_eq_one_right this
      rw [h2, h3]
    obtain ⟨ta, hta, -, hxa⟩ := C.TC_conj_form hx₀T hx₀S ha ha1
    obtain ⟨tb, htb, -, hxb⟩ := C.TC_conj_form hx₀T hx₀S ht htne
    obtain ⟨tc, htc, -, hxc⟩ := C.TC_conj_form hx₀T hx₀S (mul_mem ha ht) hat1
    have hz2 : C.zU * C.zU = 1 := by rw [← pow_two]; exact C.zU_sq
    have hzb : tb * C.zU = C.zU * tb := C.TC_comm_H htb (C.blockU_le_H C.zU_mem)
    have e1 : x₀⁻¹ * (a * t) * x₀ = (x₀⁻¹ * a * x₀) * (x₀⁻¹ * t * x₀) := by group
    rw [hxa, hxb, hxc] at e1
    have e2 : tc * C.zU = ta * tb := by
      rw [e1]
      calc ta * C.zU * (tb * C.zU) = ta * (C.zU * tb) * C.zU := by group
        _ = ta * (tb * C.zU) * C.zU := by rw [hzb]
        _ = ta * tb * (C.zU * C.zU) := by group
        _ = ta * tb := by rw [hz2, mul_one]
    have hzT : C.zU ∈ blockTC T S L := by
      have : C.zU = tc⁻¹ * (ta * tb) := by rw [← e2]; group
      rw [this]
      exact mul_mem (inv_mem htc) (mul_mem hta htb)
    have hmem : C.zU ∈ blockTC T S L ⊓ blockU L := ⟨hzT, C.zU_mem⟩
    rw [C.F.TC_inf_U] at hmem
    exact C.zU_ne_one hmem
  refine ⟨t, ht, htne, fun a ha => ?_, fun x hxT hxS => ?_⟩
  · by_cases ha1 : a = 1
    · exact Or.inl ha1
    · exact Or.inr (hsmall a ha ha1)
  · obtain ⟨t₁, ht₁, ht₁1, hx⟩ := C.TC_conj_form hxT hxS ht htne
    rw [hx, hsmall t₁ ht₁ ht₁1]

theorem zU_central_T (C : StdCfg T M H S L) (hne : blockTC T S L ≠ ⊥) {y : G} (hy : y ∈ T) :
    y * C.zU * y⁻¹ = C.zU := by
  by_cases hyS : y ∈ S
  · exact C.zU_central_S hyS
  · obtain ⟨t, ht, ht1, -, hx⟩ := C.TC_structure hne
    have hy2 : y * y ∈ S := mul_self_mem_of_relIndex_two C.F.index_two hy hyS
    have h1 := hx y hy hyS
    have h2 : y⁻¹ * (y⁻¹ * t * y) * y = t := by
      have hc : t * (y * y) = (y * y) * t := C.TC_comm_H ht (C.hcs.sylow.le hy2)
      calc y⁻¹ * (y⁻¹ * t * y) * y = (y * y)⁻¹ * (t * (y * y)) := by group
        _ = (y * y)⁻¹ * ((y * y) * t) := by rw [hc]
        _ = t := by group
    have h3 : y⁻¹ * (t * C.zU) * y = (y⁻¹ * t * y) * (y⁻¹ * C.zU * y) := by group
    rw [h1] at h2
    rw [h1] at h3
    have h4 : t * C.zU * (y⁻¹ * C.zU * y) = t := by rw [← h3, h2]
    have h5 : C.zU * (y⁻¹ * C.zU * y) = 1 := by
      calc C.zU * (y⁻¹ * C.zU * y) = t⁻¹ * (t * C.zU * (y⁻¹ * C.zU * y)) := by group
        _ = t⁻¹ * t := by rw [h4]
        _ = 1 := by group
    have hz2 : C.zU * C.zU = 1 := by rw [← pow_two]; exact C.zU_sq
    have h6 : y⁻¹ * C.zU * y = C.zU := by
      rw [eq_inv_of_mul_eq_one_right h5]
      exact inv_eq_of_mul_eq_one_right hz2
    calc y * C.zU * y⁻¹ = y * (y⁻¹ * C.zU * y) * y⁻¹ := by rw [h6]
      _ = C.zU := by group

end StdCfg

end CFSG.QuasithinUnique.A5
