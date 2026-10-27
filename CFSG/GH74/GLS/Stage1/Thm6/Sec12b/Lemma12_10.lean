module

public import CFSG.GH74.GLS.Stage1.Thm6.Sec12b.Lemma12_10b

public section

namespace CFSG.GH74.GLS.Stage1.Thm6.Sec12b

open Subgroup CFSG.GH74.GLS.Stage1.Thm6 CFSG.GH74.GLS.Stage1.Thm6.Sec12
open scoped commutatorElement

variable {G : Type*} [Group G] [Finite G] {x z : G} {S T P Q Rd F U : Subgroup G}

theorem EV_eq_T (h : HBase G x S T P Q Rd F) (h127 : After127 G x z S T P Q Rd F)
    (h8 : Nat.card (omegaZ T) = 8) {V : Subgroup G} (hVP : V ≤ P) (hV : IsFour V) :
    V ⊔ Subgroup.zpowers x = T := by
  have hTZ := h127.T_eq_Z h8
  have hT8 : Nat.card ↥T = 8 := (congrArg (fun K : Subgroup G => Nat.card ↥K) hTZ).trans h8
  exact Subgroup.eq_of_le_of_card_ge (E_le_T h hVP) (by rw [hT8, card_E h hVP hV])

omit [Finite G] in
theorem conj_mem_iff_of_mem {t : G} (ht : t ∈ T) : ∀ s : G, s ∈ T ↔ t * s * t⁻¹ ∈ T := by
  intro s
  refine ⟨fun hs => T.mul_mem (T.mul_mem ht hs) (T.inv_mem ht), fun hs => ?_⟩
  have := T.mul_mem (T.mul_mem (T.inv_mem ht) hs) ht
  simpa [mul_assoc] using this

theorem a_normalizes_EV (h : HBase G x S T P Q Rd F) (hz : HZ T P z)
    (h127 : After127 G x z S T P Q Rd F) (hU : HU S T U) (h129 : 2 < T.relIndex S)
    (hE8 : IP_E8_two T) (hexp : IP_cent_P_exp T P Q) {a : G} (haS : a ∈ S) (haT : a ∉ T)
    (haTn : ∀ t : G, t ∈ T ↔ a * t * a⁻¹ ∈ T) {V : Subgroup G} (hVP : V ≤ P) (hV : IsFour V) :
    a ∈ Subgroup.normalizer ((V ⊔ Subgroup.zpowers x : Subgroup G) : Set G) := by
  rcases h127.card_Z with h4 | h8
  · have hxU := x_not_mem_U h hU h129
    have hzU := z_mem_U h hz h127 h4 hexp hU haS haT haTn
    refine normalizes_EV h hE8 hU hxU hVP hV haTn ?_
    apply mem_normalizer_of_forward
    intro e he
    have hle : U ⊔ Subgroup.zpowers x ≤ Hconj a (U ⊔ Subgroup.zpowers x) := by
      refine sup_le (fun u hu => mem_Hconj.2 (Subgroup.mem_sup_left (hU.normal.2 a haS u hu)))
        ((Subgroup.zpowers_le).2 (mem_Hconj.2 ?_))
      have hZ : a * x * a⁻¹ ∈ omegaZ T := omegaZ_conj_mem haTn h.x_mem_Z
      rw [h127.Z_eq h4] at hZ
      have hZle : Subgroup.zpowers x ⊔ Subgroup.zpowers z ≤ U ⊔ Subgroup.zpowers x :=
        sup_le le_sup_right ((Subgroup.zpowers_le).2 (Subgroup.mem_sup_left hzU))
      exact hZle hZ
    exact mem_Hconj.1 (hle he)
  · rw [EV_eq_T h h127 h8 hVP hV, Subgroup.mem_normalizer_iff]
    intro t
    exact haTn t

theorem EV_normal (h : HBase G x S T P Q Rd F) (h127 : After127 G x z S T P Q Rd F)
    (hU : HU S T U) (h129 : 2 < T.relIndex S) (hE8 : IP_E8_two T) {V : Subgroup G}
    (hVP : V ≤ P) (hV : IsFour V) : NormalIn (V ⊔ Subgroup.zpowers x) T := by
  refine ⟨E_le_T h hVP, fun t ht e he => ?_⟩
  rcases h127.card_Z with h4 | h8
  · have hxU := x_not_mem_U h hU h129
    have hEUnorm : NormalIn (U ⊔ Subgroup.zpowers x) T :=
      normalIn_sup_zpowers h.x_mem_T h.x_central hU.le_T
        (fun t ht u hu => hU.normal.2 t (h.T_le_S ht) u hu)
    have htU : t ∈ Subgroup.normalizer ((U ⊔ Subgroup.zpowers x : Subgroup G) : Set G) :=
      mem_normalizer_of_forward (fun e he => hEUnorm.2 t ht e he)
    exact (Subgroup.mem_normalizer_iff.1
      (normalizes_EV h hE8 hU hxU hVP hV (conj_mem_iff_of_mem ht) htU) e).1 he
  · rw [EV_eq_T h h127 h8 hVP hV] at he ⊢
    exact T.mul_mem (T.mul_mem ht he) (T.inv_mem ht)

theorem V_normal (h : HBase G x S T P Q Rd F) {V : Subgroup G}
    (hEn : NormalIn (V ⊔ Subgroup.zpowers x) T) (hVP : V ≤ P) {t : G} (ht : t ∈ T) {v : G} (hv : v ∈ V) : t * v * t⁻¹ ∈ V := by
  have h1 : t * v * t⁻¹ ∈ V ⊔ Subgroup.zpowers x := hEn.2 t ht v (Subgroup.mem_sup_left hv)
  have h2 : t * v * t⁻¹ ∈ P := h.P_normal.2 t ht v (hVP hv)
  have hc : ∀ a ∈ V, ∀ b ∈ Subgroup.zpowers x, a * b = b * a := by
    intro a ha b hb
    obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.1 hb
    exact (Commute.zpow_right
      (show Commute a x from (h.x_central a (h.P_le_T (hVP ha))).symm) k).eq
  obtain ⟨u, hu, b, hb, he⟩ := mem_sup_of_commute hc h1
  rcases zpowers_sq_cases h.x_sq hb with rfl | rfl
  · rw [he]; simpa using hu
  · exfalso
    apply h.x_not_mem_P
    rw [he] at h2
    have := P.mul_mem (P.inv_mem (hVP hu)) h2
    simpa [mul_assoc] using this

theorem card_T_le (h : HBase G x S T P Q Rd F) (hz : HZ T P z) {V : Subgroup G} (hzV : z ∈ V)
    (hVP : V ≤ P) (hV : IsFour V)
    (hEc : T ⊓ Subgroup.centralizer ((V ⊔ Subgroup.zpowers x : Subgroup G) : Set G) =
      V ⊔ Subgroup.zpowers x)
    (hVn : ∀ t ∈ T, ∀ v ∈ V, t * v * t⁻¹ ∈ V) : Nat.card T ≤ 16 := by
  have hz1 : z ≠ 1 := hz.z_ne_one
  have hc4 : (V : Set G).ncard = 4 := by
    rw [← Nat.card_coe_set_eq]; exact hV.2
  have hex : ∃ w ∈ (V : Set G), w ∉ ({1, z} : Set G) :=
    Set.exists_mem_notMem_of_ncard_lt_ncard (by rw [Set.ncard_pair hz1.symm, hc4]; norm_num)
      (Set.toFinite _)
  obtain ⟨w, hwV, hw⟩ := hex
  have hw1 : w ≠ 1 := fun e => hw (Or.inl e)
  have hwz : w ≠ z := fun e => hw (Or.inr e)
  have hE8 := card_E h hVP hV
  have hEab := isElemAb2_sup_zpowers hV h.x_sq (fun v hv => h.x_central v (h.P_le_T (hVP hv)))
  have hTC : T ⊓ Subgroup.centralizer ({w} : Set G) = V ⊔ Subgroup.zpowers x := by
    apply le_antisymm
    · rintro t ⟨htT, htw⟩
      rw [← hEc]
      refine ⟨htT, ?_⟩
      have hV' : V = Subgroup.zpowers z ⊔ Subgroup.zpowers w :=
        isFour_eq_pair hV hzV hwV hz1 hw1 hwz.symm
      have hEle : V ⊔ Subgroup.zpowers x ≤ Subgroup.centralizer ({t} : Set G) := by
        apply sup_le
        · rw [hV']
          refine sup_le ((Subgroup.zpowers_le).2 ?_) ((Subgroup.zpowers_le).2 ?_)
          · exact Subgroup.mem_centralizer_singleton_iff.2 (hz.z_central t htT)
          · exact Subgroup.mem_centralizer_singleton_iff.2
              (Subgroup.mem_centralizer_singleton_iff.1 htw).symm
        · exact (Subgroup.zpowers_le).2
            (Subgroup.mem_centralizer_singleton_iff.2 (h.x_central t htT))
      exact Subgroup.mem_centralizer_iff.2
        (fun e he => Subgroup.mem_centralizer_singleton_iff.1 (hEle he))
    · intro e he
      refine ⟨E_le_T h hVP he, Subgroup.mem_centralizer_singleton_iff.2 ?_⟩
      exact (hEab e he).2 w (Subgroup.mem_sup_left hwV)
  have hcount := ncard_conj_mul_card_inf_centralizer T w
  rw [hTC, hE8] at hcount
  have hsub : {y | ∃ n ∈ T, n * w * n⁻¹ = y} ⊆ ((V : Set G) \ {1, z}) := by
    rintro y ⟨n, hn, rfl⟩
    refine ⟨hVn n hn w hwV, ?_⟩
    rintro (h1 | h1)
    · exact hw1 (conj_inj n (h1.trans (by group)))
    · have hnz : n * z * n⁻¹ = z := by rw [← hz.z_central n hn]; group
      exact hwz (conj_inj n (h1.trans hnz.symm))
  have hcard : ((V : Set G) \ {1, z}).ncard = 2 := by
    have hsubV : ({1, z} : Set G) ⊆ (V : Set G) := by
      intro e he
      rcases he with rfl | rfl
      · exact V.one_mem
      · exact hzV
    rw [Set.ncard_sdiff hsubV, hc4, Set.ncard_pair hz1.symm]
  have hle2 : {y | ∃ n ∈ T, n * w * n⁻¹ = y}.ncard ≤ 2 := by
    calc _ ≤ ((V : Set G) \ {1, z}).ncard := Set.ncard_le_ncard hsub (Set.toFinite _)
      _ = 2 := hcard
  omega

omit [Finite G] in
theorem sup_zpowers_cases {V : Subgroup G} {x : G} (hx2 : x * x = 1)
    (hxV : ∀ w ∈ V, x * w = w * x) {e : G} (he : e ∈ V ⊔ Subgroup.zpowers x) :
    e ∈ V ∨ ∃ w ∈ V, e = x * w := by
  have hc : ∀ u ∈ V, ∀ v ∈ Subgroup.zpowers x, u * v = v * u := comm_zpowers hxV
  obtain ⟨u, hu, v, hv, rfl⟩ := mem_sup_of_commute hc he
  rcases zpowers_sq_cases hx2 hv with rfl | rfl
  · left; simpa using hu
  · right; exact ⟨u, hu, (hxV u hu).symm⟩

theorem f_x_comm (h : HBase G x S T P Q Rd F) (hf3 : IP_f3 x P) {V : Subgroup G} (hVP : V ≤ P)
    (hV : IsFour V) :
    ∃ f : G, Is3 f ∧ f ∈ Subgroup.centralizer ({x} : Set G) ∧
      f ∈ Subgroup.normalizer ((V ⊔ Subgroup.zpowers x : Subgroup G) : Set G) ∧
        ⁅Subgroup.zpowers f, V ⊔ Subgroup.zpowers x⁆ = V := by
  obtain ⟨f, hf3', hfx, hfV, hfn⟩ := hf3 V hVP hV
  have hxV : ∀ w ∈ V, x * w = w * x := fun w hw => h.x_central w (h.P_le_T (hVP hw))
  have hfx' : f * x * f⁻¹ = x := by rw [hfx]; group
  have hfN : f ∈ Subgroup.normalizer ((V ⊔ Subgroup.zpowers x : Subgroup G) : Set G) := by
    apply mem_normalizer_of_forward
    intro e he
    have hle : V ⊔ Subgroup.zpowers x ≤ Hconj f (V ⊔ Subgroup.zpowers x) :=
      sup_le (fun w hw => mem_Hconj.2 (Subgroup.mem_sup_left (hfV w hw)))
        ((Subgroup.zpowers_le).2 (mem_Hconj.2 (by
          rw [hfx']; exact Subgroup.mem_sup_right (Subgroup.mem_zpowers x))))
    exact mem_Hconj.1 (hle he)
  have hfNV : f ∈ Subgroup.normalizer (V : Set G) := mem_normalizer_of_forward hfV
  refine ⟨f, hf3', Subgroup.mem_centralizer_singleton_iff.2 hfx, hfN, ?_⟩
  obtain ⟨w0, hw0, hw0f⟩ := hfn
  have hw01 : w0 ≠ 1 := by
    rintro rfl
    exact hw0f (by group)
  obtain ⟨p1, p2, T'⟩ := exists_tri hV hf3' hfV ⟨w0, hw0, hw0f⟩ hw0 hw01
  have hw02 := (hV.1 w0 hw0).1
  have hp12 := (hV.1 p1 T'.m1).1
  have hp22 := (hV.1 p2 T'.m2).1
  apply le_antisymm
  · rw [Subgroup.commutator_le]
    intro g1 hg1 g2 hg2
    have hg1' : g1 ∈ Subgroup.centralizer ({x} : Set G) ⊓
        Subgroup.normalizer (V : Set G) := by
      have : Subgroup.zpowers f ≤ Subgroup.centralizer ({x} : Set G) ⊓
          Subgroup.normalizer (V : Set G) :=
        (Subgroup.zpowers_le).2 ⟨Subgroup.mem_centralizer_singleton_iff.2 hfx, hfNV⟩
      exact this hg1
    have hg1x : g1 * x * g1⁻¹ = x := by
      have := Subgroup.mem_centralizer_singleton_iff.1 hg1'.1
      rw [this]; group
    have hg1V : ∀ w ∈ V, g1 * w * g1⁻¹ ∈ V := fun w hw =>
      (Subgroup.mem_normalizer_iff.1 hg1'.2 w).1 hw
    rw [commutatorElement_def]
    rcases sup_zpowers_cases h.x_sq hxV hg2 with hv | ⟨w, hw, rfl⟩
    · exact V.mul_mem (hg1V g2 hv) (V.inv_mem hv)
    · have hc : g1 * w * g1⁻¹ * w⁻¹ ∈ V := V.mul_mem (hg1V w hw) (V.inv_mem hw)
      have e : g1 * (x * w) * g1⁻¹ * (x * w)⁻¹ = x * (g1 * w * g1⁻¹ * w⁻¹) * x⁻¹ := by
        calc g1 * (x * w) * g1⁻¹ * (x * w)⁻¹ = (g1 * x * g1⁻¹) * (g1 * w * g1⁻¹) * w⁻¹ * x⁻¹ := by
              group
          _ = x * (g1 * w * g1⁻¹ * w⁻¹) * x⁻¹ := by rw [hg1x]; group
      rw [e]
      have hxc : x * (g1 * w * g1⁻¹ * w⁻¹) = (g1 * w * g1⁻¹ * w⁻¹) * x := hxV _ hc
      rw [hxc]
      simpa using hc
  · intro v hv
    have hfz : f ∈ Subgroup.zpowers f := Subgroup.mem_zpowers f
    have hE : ∀ w ∈ V, w ∈ V ⊔ Subgroup.zpowers x := fun w hw => Subgroup.mem_sup_left hw
    rcases T'.allV v hv with h1 | h1 | h1 | h1
    · rw [h1]; exact Subgroup.one_mem _
    ·
      have := Subgroup.commutator_mem_commutator hfz (hE p1 T'.m1)
      rw [commutatorElement_def, T'.f1, inv_eq_of_mul_eq_one_right hp12] at this
      have e : p2 * p1 = w0 := by
        rw [← T'.m01, mul_assoc, hp12, mul_one]
      rw [h1, ← e]
      exact this
    ·
      have := Subgroup.commutator_mem_commutator hfz (hE p2 T'.m2)
      rw [commutatorElement_def, T'.f2, inv_eq_of_mul_eq_one_right hp22] at this
      have e : w0 * p2 = p1 := by
        rw [← T'.m01, ← mul_assoc, hw02, one_mul]
      rw [h1, ← e]
      exact this
    ·
      have := Subgroup.commutator_mem_commutator hfz (hE w0 hw0)
      rw [commutatorElement_def, T'.f0, inv_eq_of_mul_eq_one_right hw02] at this
      have e : p1 * w0 = p2 := by
        rw [← T'.m01, (hV.1 w0 hw0).2 p1 T'.m1]
      rw [h1, ← e]
      exact this

theorem lemma_12_10 :
    ∀ (G : Type) [Group G] [Finite G] (x : G) (S T P Q Rd F U : Subgroup G) (z : G),
      HBase G x S T P Q Rd F → HZ T P z → HU S T U → After127 G x z S T P Q Rd F →
      2 < T.relIndex S → IP_P_four P → IP_f3 x P → IP_z_V z P → IP_cent_P_exp T P Q →
      IP_E8_two T → IP_outer x T Rd → IP_cent_four T P Q Rd → IP_P_closed x T P →
      ∃ V : Subgroup G, V ≤ P ∧ IsFour V ∧ x ∉ V ∧ (∀ t ∈ T, ∀ v ∈ V, t * v * t⁻¹ ∈ V) ∧
        IsSylow2In (V ⊔ Subgroup.zpowers x)
          (Subgroup.centralizer ((V ⊔ Subgroup.zpowers x : Subgroup G) : Set G)) ∧
        T ⊓ Subgroup.centralizer ((V ⊔ Subgroup.zpowers x : Subgroup G) : Set G) =
          V ⊔ Subgroup.zpowers x ∧
        Nat.card T ≤ 16 ∧
        (∃ f : G, Is3 f ∧ f ∈ Subgroup.centralizer ({x} : Set G) ∧
          f ∈ Subgroup.normalizer ((V ⊔ Subgroup.zpowers x : Subgroup G) : Set G) ∧
          ⁅Subgroup.zpowers f, V ⊔ Subgroup.zpowers x⁆ = V) ∧
        (∀ v ∈ V, ∃ g : G, g ∈ Subgroup.centralizer (V : Set G) ∧ g * x * g⁻¹ = x * v) := by
  intro G _ _ x S T P Q Rd F U z h hz hU h127 h129 hP4 hf3 hzV hexp hE8 hout hcf hclosed
  obtain ⟨V, hVP, hV⟩ := hP4
  obtain ⟨a, haS, haT, haTn, _⟩ := h127.exists_a
  have hzV' : z ∈ V := hzV V hVP hV
  have haN := a_normalizes_EV h hz h127 hU h129 hE8 hexp haS haT haTn hVP hV
  have hEn := EV_normal h h127 hU h129 hE8 hVP hV
  have hVn : ∀ t ∈ T, ∀ v ∈ V, t * v * t⁻¹ ∈ V := fun t ht v hv => V_normal h hEn hVP ht hv
  have hsyl := EV_isSylow h h127 hout hcf hclosed hf3 hzV hVP hV haS haT haN
  have hEc : T ⊓ Subgroup.centralizer ((V ⊔ Subgroup.zpowers x : Subgroup G) : Set G) =
      V ⊔ Subgroup.zpowers x := by
    have hpg : IsPGroup 2 ↥(T ⊓ Subgroup.centralizer ((V ⊔ Subgroup.zpowers x : Subgroup G) :
        Set G)) := h.T_pgroup.of_injective (Subgroup.inclusion inf_le_left)
      (Subgroup.inclusion_injective inf_le_left)
    exact sylow2_eq_of_le hsyl hpg (le_inf (E_le_T h hVP) hsyl.1) inf_le_right
  refine ⟨V, hVP, hV, fun hx => h.x_not_mem_P (hVP hx), hVn, hsyl, hEc,
    card_T_le h hz hzV' hVP hV hEc hVn, f_x_comm h hf3 hVP hV, ?_⟩
  intro v hv
  obtain ⟨g, hg, _, hgx⟩ := fusion_V h h127 hf3 hzV hVP hV haS haT haN v hv
  exact ⟨g, hg, hgx⟩

end CFSG.GH74.GLS.Stage1.Thm6.Sec12b
