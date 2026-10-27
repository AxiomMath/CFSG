module

public import CFSG.CGT.PushingUpLit.A78T2.K1
public import CFSG.CGT.PushingUpLit.A78T2.Cubes
public import CFSG.CGT.PushingUpLit.A78Sp4.F410Two

public section

namespace CFSG.CGT.PushingUpLit.A78T2

open CFSG.Assembly CFSG.ABGLocalTools
open CFSG.CGT.PushingUpLit.A78Sp4 (cj ElemAb2 mul_mem_cj mem_normalizer_of_cj elemAb2_cj card_cj
  cj_mono cj_sup_eq pCoreOf_le_of_isSylowOf qCenter mem_qCenter qCenter_conj_mem_of mem_cj_iff
  cj_cj exists_conj_le_of_isSylowOf)
open scoped commutatorElement

variable {G : Type} [Group G] [Finite G] {L L₂ V V₂ Z J T S M M₂ : Subgroup G} {e : ℕ}

theorem T2Base.inv_mul_mem_T (h : T2Base G V V₂ Z J T S M M₂ e) {x y : G} (hx : x ∈ S)
    (hy : y ∈ S) (hxT : x ∉ T) (hyT : y ∉ T) : x⁻¹ * y ∈ T := by
  have hidx : (T.subgroupOf S).index = 2 := by
    have h2 : (T.subgroupOf S).index ≤ 2 := h.index
    have h0 : (T.subgroupOf S).index ≠ 0 := Subgroup.index_ne_zero_of_finite
    have h1 : (T.subgroupOf S).index ≠ 1 := by
      rw [Ne, Subgroup.index_eq_one]
      intro htop
      obtain ⟨s, hs, hsT⟩ := h.exists_swap
      apply hsT
      have : (⟨s, hs⟩ : S) ∈ T.subgroupOf S := by rw [htop]; trivial
      exact Subgroup.mem_subgroupOf.1 this
    omega
  have key := Subgroup.mul_mem_iff_of_index_two hidx (a := (⟨x, hx⟩ : S)⁻¹) (b := ⟨y, hy⟩)
  have hx' : ((⟨x, hx⟩ : S)⁻¹) ∉ T.subgroupOf S := fun h' => hxT (by
    have := Subgroup.mem_subgroupOf.1 h'
    simpa using this)
  have hy' : (⟨y, hy⟩ : S) ∉ T.subgroupOf S := fun h' => hyT (Subgroup.mem_subgroupOf.1 h')
  have := key.2 ⟨fun h' => absurd h' hx', fun h' => absurd h' hy'⟩
  simpa using Subgroup.mem_subgroupOf.1 this

theorem T2Side.mem_normalizer_J_of_comm (hs : T2Side G L V Z J T M e) {z₀ : G} (hz₀ : z₀ ∈ Z)
    (hz₀1 : z₀ ≠ 1) {m : G} (hm : m ∈ M) (hmz : m * z₀ = z₀ * m) :
    m ∈ Subgroup.normalizer (J : Set G) := by
  refine mem_normalizer_of_conj_mem fun x hx => ?_
  have hxJ : x ∈ L ⊓ Subgroup.centralizer ({z₀} : Set G) := by rw [hs.cent_L z₀ hz₀ hz₀1]; exact hx
  rw [← hs.cent_L z₀ hz₀ hz₀1]
  have h1 : x * z₀ = z₀ * x := Subgroup.mem_centralizer_singleton_iff.1 hxJ.2
  refine ⟨hs.conj_mem_L hm hxJ.1, Subgroup.mem_centralizer_singleton_iff.2 ?_⟩
  calc m * x * m⁻¹ * z₀ = m * x * (m⁻¹ * z₀ * m) * m⁻¹ := by group
    _ = m * x * z₀ * m⁻¹ := by
        rw [show m⁻¹ * z₀ * m = z₀ by rw [mul_assoc, ← hmz]; group]
    _ = m * z₀ * x * m⁻¹ := by rw [mul_assoc m x z₀, h1, ← mul_assoc]
    _ = z₀ * (m * x * m⁻¹) := by rw [hmz]; group

theorem exists_pow_six_ne_one {K : Type*} [Field K] [Finite K] (hK : 7 < Nat.card K) :
    ∃ t : K, t ≠ 0 ∧ t ^ 6 ≠ 1 := by
  classical
  have hp0 : (Polynomial.X ^ 6 - Polynomial.C 1 : Polynomial K) ≠ 0 :=
    Polynomial.X_pow_sub_C_ne_zero (by norm_num) 1
  have hdeg : (Polynomial.X ^ 6 - Polynomial.C 1 : Polynomial K).natDegree = 6 :=
    Polynomial.natDegree_X_pow_sub_C
  obtain ⟨t, ht⟩ := CFSG.CGT.PushingUpLit.A78Sp4.exists_avoid
    (insert 0 (Polynomial.X ^ 6 - Polynomial.C 1 : Polynomial K).roots.toFinset) (by
      calc _ ≤ (Polynomial.X ^ 6 - Polynomial.C 1 : Polynomial K).roots.toFinset.card + 1 :=
            Finset.card_insert_le _ _
        _ ≤ (Polynomial.X ^ 6 - Polynomial.C 1 : Polynomial K).natDegree + 1 :=
            Nat.add_le_add_right ((Multiset.toFinset_card_le _).trans
              (Polynomial.card_roots' _)) 1
        _ < Nat.card K := by rw [hdeg]; omega)
  rw [Finset.mem_insert, not_or, Multiset.mem_toFinset, Polynomial.mem_roots hp0] at ht
  refine ⟨t, ht.1, fun h6 => ht.2 ?_⟩
  simp [h6]

section D

variable {a b c : G → GaloisField 2 e}

omit [Finite G] in
theorem T2Tori.exists_d (hH : T2Heis G J V V₂ Z (GaloisField 2 e) a b c)
    (hT : T2Tori G J Z L L₂ (GaloisField 2 e) a b c) {t : GaloisField 2 e} (ht : t ≠ 0) :
    ∃ d : G, (∀ j ∈ J, d * j * d⁻¹ ∈ J) ∧
      (∀ j ∈ J, a (d * j * d⁻¹) = (t ^ 3)⁻¹ * a j ∧ b (d * j * d⁻¹) = t ^ 3 * b j) ∧
      ∀ z ∈ Z, d * z * d⁻¹ = z := by
  obtain ⟨x, -, hxJ, hxab, hxZ⟩ := hT.torus₁ t ht
  obtain ⟨y, -, hyJ, hyab, hyZ⟩ := hT.torus₂ t⁻¹ (inv_ne_zero ht)
  have e1 : ∀ j, (x * y) * j * (x * y)⁻¹ = x * (y * j * y⁻¹) * x⁻¹ := fun j => by group
  refine ⟨x * y, fun j hj => ?_, fun j hj => ?_, fun z hz => ?_⟩
  · rw [e1]; exact hxJ _ (hyJ j hj)
  · rw [e1, (hxab _ (hyJ j hj)).1, (hxab _ (hyJ j hj)).2, (hyab j hj).1, (hyab j hj).2]
    constructor
    · field_simp
    · field_simp
  · rw [e1]
    have h1 := hyZ z hz
    have h2 := hxZ _ h1.1
    refine hH.inj_c _ h2.1 z hz ?_
    rw [h2.2, h1.2]
    field_simp

end D

theorem T2Loc.J_le_O2_cent (h : T2Loc G L L₂ V V₂ Z J T S M M₂ e) {z : G} (hz : z ∈ Z)
    (hz1 : z ≠ 1) (hcen : ∀ s ∈ S, s * z = z * s) :
    J ≤ CFSG.Open.pCoreOf 2 (Subgroup.centralizer ({z} : Set G)) := by
  obtain ⟨a, b, c, hH, hT⟩ := h.coords
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  set C := Subgroup.centralizer ({z} : Set G) with hC
  set Q := CFSG.Open.pCoreOf 2 C with hQ
  have hinf := h.base.inf
  have hZJ := h.base.Z_le_J
  have hJS := h.base.J_le_S
  have hq : Nat.card (GaloisField 2 e) = 2 ^ e :=
    GaloisField.card 2 e (by have := h.three_le; omega)
  have he3 := h.three_le
  have h2F : (2 : GaloisField 2 e) = 0 := CFSG.CGT.PushingUpLit.A78Sp4.charTwo_two_eq_zero
  have hSC : S ≤ C := fun s hs => Subgroup.mem_centralizer_singleton_iff.2 (hcen s hs)
  have hQS : Q ≤ S := pCoreOf_le_of_isSylowOf (h.base.sylow.of_le hSC le_top)
  have hQp : IsPGroup 2 Q := CFSG.LieType.BorelTits.pCoreOf_isPGroup 2 C
  have hQn : ∀ g ∈ C, ∀ q ∈ Q, g * q * g⁻¹ ∈ Q := fun g hg q hq =>
    (Subgroup.mem_normalizer_iff.1 (CFSG.LieType.BorelTits.le_normalizer_pCoreOf 2 C hg) q).1 hq
  have hzV := h.base.Z_le_V hz
  have hz2 : z * z = 1 := (h.base.elem_V z hzV z hzV).2
  have hcent : ∀ g ∈ C, (∀ q ∈ Q, g * q = q * g) → g ∈ Q := fun g hg hgq =>
    CFSG.CGT.PushingUpLit.A78Sp4.cent_le_pCoreOf h.charTwo hz2 hz1
      ⟨hg, Subgroup.mem_centralizer_iff.2 fun q hq => (hgq q hq).symm⟩
  have hJp : IsPGroup 2 J := h.base.isPGroup_S.to_le hJS
  have hJC : J ≤ C := fun j hj => hSC (hJS hj)
  have hcomm : ∀ q ∈ Q, ∀ j ∈ J, ⁅q, j⁆ ∈ Q ⊓ J := by
    intro q hq j hj
    refine ⟨?_, ?_⟩
    · have h1 := hQn j (hJC hj) q⁻¹ (Q.inv_mem hq)
      have : ⁅q, j⁆ = q * (j * q⁻¹ * j⁻¹) := by simp [commutatorElement_def, mul_assoc]
      rw [this]
      exact Q.mul_mem hq h1
    · have : ⁅q, j⁆ = (q * j * q⁻¹) * j⁻¹ := by simp [commutatorElement_def, mul_assoc]
      rw [this]
      exact J.mul_mem (h.base.conj_J (hQS hq) hj) (J.inv_mem hj)
  set W := Q ⊓ J with hW
  have hWZ : ¬ W ≤ Z := by
    intro hle
    have hQJ : Q ≤ J := fun q hq => h.base.cent_S q (hQS hq) fun j hj => hle (hcomm q hq j hj)
    have hQZ : Q ≤ Z := fun q hq => hle ⟨hq, hQJ hq⟩
    have hJQ : J ≤ Q := fun j hj => hcent j (hJC hj) fun q hq =>
      (hH.central hinf hZJ h.base.comm_mem (hQZ hq) hj).symm
    exact h.base.not_V_le_Z ((h.base.V_le_J.trans hJQ).trans hQZ)
  have hZW : Z ≤ W := by
    obtain ⟨x, hxW, hxZ⟩ := Set.not_subset.1 hWZ
    have hxJ : x ∈ J := hxW.2
    intro z' hz'
    have key : ∃ j ∈ J, c ⁅x, j⁆ = c z' := by
      by_cases hax : a x = 0
      · have hbx : b x ≠ 0 := fun hb => hxZ (hH.mem_Z hinf hxJ hax hb)
        obtain ⟨j, hj, haj, hbj⟩ := hH.surj_ab (c z' / b x) 0
        refine ⟨j, hj, ?_⟩
        rw [hH.comm x hxJ j hj, hax, hbj, haj]
        field_simp
        ring
      · obtain ⟨j, hj, haj, hbj⟩ := hH.surj_ab 0 (c z' / a x)
        refine ⟨j, hj, ?_⟩
        rw [hH.comm x hxJ j hj, haj, hbj]
        field_simp
        ring
    obtain ⟨j, hj, hjc⟩ := key
    have := hH.inj_c _ (h.base.comm_mem x hxJ j hj) z' hz' hjc
    rw [← this]
    exact hcomm x hxW.1 j hj
  have hcrit : ∀ j ∈ J, ∀ w ∈ W, a w = a j → b w = b j → j ∈ W := by
    intro j hj w hw ha hb
    have := hZW (hH.inv_mul_mem_Z hinf hw.2 hj ha hb)
    have e1 : j = w * (w⁻¹ * j) := by group
    rw [e1]
    exact W.mul_mem hw this
  have hD : ∀ t : GaloisField 2 e, t ≠ 0 → ∀ w ∈ W,
      ∃ w' ∈ W, a w' = (t ^ 3)⁻¹ * a w ∧ b w' = t ^ 3 * b w := by
    intro t ht w hw
    obtain ⟨d, hdJ, hdab, hdZ⟩ := hT.exists_d hH ht
    have hdz : d ∈ C := by
      rw [Subgroup.mem_centralizer_singleton_iff]
      have := hdZ z hz
      calc d * z = d * z * d⁻¹ * d := by group
        _ = z * d := by rw [this]
    exact ⟨d * w * d⁻¹, ⟨hQn d hdz w hw.1, hdJ w hw.2⟩, (hdab w hw.2).1, (hdab w hw.2).2⟩
  let B₁ : AddSubgroup (GaloisField 2 e) :=
    { carrier := {r | ∃ w ∈ W, a w = r ∧ b w = 0}
      zero_mem' := ⟨1, W.one_mem, hH.a_one, hH.b_one⟩
      add_mem' := by
        rintro _ _ ⟨w₁, hw₁, rfl, hb₁⟩ ⟨w₂, hw₂, rfl, hb₂⟩
        exact ⟨w₁ * w₂, W.mul_mem hw₁ hw₂, hH.add_a _ hw₁.2 _ hw₂.2, by
          rw [hH.add_b _ hw₁.2 _ hw₂.2, hb₁, hb₂, add_zero]⟩
      neg_mem' := by
        rintro _ ⟨w, hw, rfl, hb⟩
        exact ⟨w⁻¹, W.inv_mem hw, hH.a_inv hw.2, by rw [hH.b_inv hw.2, hb, neg_zero]⟩ }
  let B₂ : AddSubgroup (GaloisField 2 e) :=
    { carrier := {s | ∃ w ∈ W, a w = 0 ∧ b w = s}
      zero_mem' := ⟨1, W.one_mem, hH.a_one, hH.b_one⟩
      add_mem' := by
        rintro _ _ ⟨w₁, hw₁, ha₁, rfl⟩ ⟨w₂, hw₂, ha₂, rfl⟩
        exact ⟨w₁ * w₂, W.mul_mem hw₁ hw₂, by
          rw [hH.add_a _ hw₁.2 _ hw₂.2, ha₁, ha₂, add_zero], hH.add_b _ hw₁.2 _ hw₂.2⟩
      neg_mem' := by
        rintro _ ⟨w, hw, ha, rfl⟩
        exact ⟨w⁻¹, W.inv_mem hw, by rw [hH.a_inv hw.2, ha, neg_zero], hH.b_inv hw.2⟩ }
  have hB₁ : ∀ t : GaloisField 2 e, t ≠ 0 → ∀ r ∈ B₁, t ^ 3 * r ∈ B₁ := by
    rintro t ht _ ⟨w, hw, rfl, hb⟩
    obtain ⟨w', hw', ha', hb'⟩ := hD t⁻¹ (inv_ne_zero ht) w hw
    refine ⟨w', hw', ?_, by rw [hb', hb, mul_zero]⟩
    rw [ha', inv_pow, inv_inv]
  have hB₂ : ∀ t : GaloisField 2 e, t ≠ 0 → ∀ s ∈ B₂, t ^ 3 * s ∈ B₂ := by
    rintro t ht _ ⟨w, hw, ha, rfl⟩
    obtain ⟨w', hw', ha', hb'⟩ := hD t ht w hw
    exact ⟨w', hw', by rw [ha', ha, mul_zero], hb'⟩
  have hspread₁ : (∃ r ∈ B₁, r ≠ 0) → V ≤ W := by
    rintro ⟨r₀, hr₀, hr₀0⟩ v hv
    have hvJ := h.base.V_le_J hv
    have hbv : b v = 0 := (hH.ker_b v hvJ).1 hv
    have hmem : a v / r₀ * r₀ ∈ B₁ := mul_mem_of_closure_cubes hq he3 B₁ hB₁ _ hr₀
    rw [div_mul_cancel₀ _ hr₀0] at hmem
    obtain ⟨w, hw, haw, hbw⟩ := hmem
    exact hcrit v hvJ w hw haw (by rw [hbw, hbv])
  have hspread₂ : (∃ s ∈ B₂, s ≠ 0) → V₂ ≤ W := by
    rintro ⟨s₀, hs₀, hs₀0⟩ v hv
    have hvJ := h.base.V₂_le_J hv
    have hav : a v = 0 := (hH.ker_a v hvJ).1 hv
    have hmem : b v / s₀ * s₀ ∈ B₂ := mul_mem_of_closure_cubes hq he3 B₂ hB₂ _ hs₀
    rw [div_mul_cancel₀ _ hs₀0] at hmem
    obtain ⟨w, hw, haw, hbw⟩ := hmem
    exact hcrit v hvJ w hw (by rw [haw, hav]) hbw
  have hcaseV : V ≤ W → W ≤ V → False := by
    intro hVW hWV
    have hQT : Q ≤ T := by
      intro q hq
      have hqM : q ∈ M := by
        rw [h.side₁.M_eq]
        refine mem_normalizer_of_conj_mem fun v hv => hWV ?_
        exact ⟨Q.mul_mem (Q.mul_mem hq (hVW hv).1) (Q.inv_mem hq),
          h.base.conj_J (hQS hq) (h.base.V_le_J hv)⟩
      rw [← h.base.S_inf_M]
      exact ⟨hQS hq, hqM⟩
    have hQJ : Q ≤ J := by
      intro q hq
      by_contra hqJ
      obtain ⟨-, v, hv, hv'⟩ := h.field.fixZ q (hQT hq) hqJ
      apply hv'
      have h1 := hWV (hcomm q hq v (h.base.V₂_le_J hv))
      have h2 : ⁅q, v⁆ ∈ V₂ := by
        have : ⁅q, v⁆ = (q * v * q⁻¹) * v⁻¹ := by simp [commutatorElement_def, mul_assoc]
        rw [this]
        refine V₂.mul_mem ?_ (V₂.inv_mem hv)
        rw [← (h.base.T_norm q (hQT hq)).2]
        exact mul_mem_cj q hv
      rw [← hinf]
      exact ⟨h1, h2⟩
    have hQV : Q ≤ V := fun q hq => hWV ⟨hq, hQJ hq⟩
    have hCM : C ≤ M := fun g hg => by
      rw [h.side₁.M_eq]
      exact mem_normalizer_of_conj_mem fun v hv => hQV (hQn g hg v (hVW hv).1)
    have hCJ : C ≤ Subgroup.normalizer (J : Set G) := fun g hg =>
      h.side₁.mem_normalizer_J_of_comm hz hz1 (hCM hg)
        (Subgroup.mem_centralizer_singleton_iff.1 hg)
    have hJQ : J ≤ Q := CFSG.LieType.BorelTits.le_pCoreOf_of_le_normalizer 2 hJC hCJ hJp
    apply h.base.not_V₂_le_Z
    intro v hv
    rw [← hinf]
    exact ⟨hQV (hJQ (h.base.V₂_le_J hv)), hv⟩
  have hcaseV₂ : V₂ ≤ W → W ≤ V₂ → False := by
    intro hVW hWV
    have hQT : Q ≤ T := by
      intro q hq
      have hqM : q ∈ M₂ := by
        rw [h.side₂.M_eq]
        refine mem_normalizer_of_conj_mem fun v hv => hWV ?_
        exact ⟨Q.mul_mem (Q.mul_mem hq (hVW hv).1) (Q.inv_mem hq),
          h.base.conj_J (hQS hq) (h.base.V₂_le_J hv)⟩
      rw [← h.base.S_inf_M₂]
      exact ⟨hQS hq, hqM⟩
    have hQJ : Q ≤ J := by
      intro q hq
      by_contra hqJ
      obtain ⟨⟨v, hv, hv'⟩, -⟩ := h.field.fixZ q (hQT hq) hqJ
      apply hv'
      have h1 := hWV (hcomm q hq v (h.base.V_le_J hv))
      have h2 : ⁅q, v⁆ ∈ V := by
        have : ⁅q, v⁆ = (q * v * q⁻¹) * v⁻¹ := by simp [commutatorElement_def, mul_assoc]
        rw [this]
        refine V.mul_mem ?_ (V.inv_mem hv)
        rw [← (h.base.T_norm q (hQT hq)).1]
        exact mul_mem_cj q hv
      rw [← hinf]
      exact ⟨h2, h1⟩
    have hQV : Q ≤ V₂ := fun q hq => hWV ⟨hq, hQJ hq⟩
    have hCM : C ≤ M₂ := fun g hg => by
      rw [h.side₂.M_eq]
      exact mem_normalizer_of_conj_mem fun v hv => hQV (hQn g hg v (hVW hv).1)
    have hCJ : C ≤ Subgroup.normalizer (J : Set G) := fun g hg =>
      h.side₂.mem_normalizer_J_of_comm hz hz1 (hCM hg)
        (Subgroup.mem_centralizer_singleton_iff.1 hg)
    have hJQ : J ≤ Q := CFSG.LieType.BorelTits.le_pCoreOf_of_le_normalizer 2 hJC hCJ hJp
    apply h.base.not_V_le_Z
    intro v hv
    rw [← hinf]
    exact ⟨hv, hQV (hJQ (h.base.V_le_J hv))⟩
  by_cases h₁ : ∃ r ∈ B₁, r ≠ 0
  · have hVW := hspread₁ h₁
    by_cases h₂ : ∃ s ∈ B₂, s ≠ 0
    · have hV₂W := hspread₂ h₂
      intro j hj
      rw [← h.base.sup] at hj
      exact (sup_le hVW hV₂W hj).1
    · exfalso
      push Not at h₂
      refine hcaseV hVW fun w hw => ?_
      obtain ⟨v, hvJ, hav, hbv⟩ := hH.surj_ab (a w) 0
      have hv : v ∈ V := (hH.ker_b v hvJ).2 hbv
      have hm : v⁻¹ * w ∈ W := W.mul_mem (W.inv_mem (hVW hv)) hw
      have ha0 : a (v⁻¹ * w) = 0 := by
        rw [hH.add_a _ (J.inv_mem hvJ) _ hw.2, hH.a_inv hvJ, hav, neg_add_cancel]
      have hb0 : b (v⁻¹ * w) = 0 := h₂ _ ⟨_, hm, ha0, rfl⟩
      have hZ' := hH.mem_Z hinf (J.mul_mem (J.inv_mem hvJ) hw.2) ha0 hb0
      have e1 : w = v * (v⁻¹ * w) := by group
      rw [e1]
      exact V.mul_mem hv (h.base.Z_le_V hZ')
  push Not at h₁
  by_cases h₂ : ∃ s ∈ B₂, s ≠ 0
  · exfalso
    have hVW := hspread₂ h₂
    refine hcaseV₂ hVW fun w hw => ?_
    obtain ⟨v, hvJ, hav, hbv⟩ := hH.surj_ab 0 (b w)
    have hv : v ∈ V₂ := (hH.ker_a v hvJ).2 hav
    have hm : v⁻¹ * w ∈ W := W.mul_mem (W.inv_mem (hVW hv)) hw
    have hb0 : b (v⁻¹ * w) = 0 := by
      rw [hH.add_b _ (J.inv_mem hvJ) _ hw.2, hH.b_inv hvJ, hbv, neg_add_cancel]
    have ha0 : a (v⁻¹ * w) = 0 := h₁ _ ⟨_, hm, rfl, hb0⟩
    have hZ' := hH.mem_Z hinf (J.mul_mem (J.inv_mem hvJ) hw.2) ha0 hb0
    have e1 : w = v * (v⁻¹ * w) := by group
    rw [e1]
    exact V₂.mul_mem hv (h.base.Z_le_V₂ hZ')
  push Not at h₂
  exfalso
  have hW0b : ∀ w ∈ W, b w = 0 → w ∈ Z := fun w hw hb =>
    hH.mem_Z hinf hw.2 (h₁ _ ⟨w, hw, rfl, hb⟩) hb
  have hW0a : ∀ w ∈ W, a w = 0 → w ∈ Z := fun w hw ha =>
    hH.mem_Z hinf hw.2 ha (h₂ _ ⟨w, hw, ha, rfl⟩)
  have hinvW : ∀ w ∈ W, w * w = 1 → w ∈ Z := by
    intro w hw hww
    rcases h.base.inv_mem w hw.2 hww with hwV | hwV₂
    · exact hW0b w hw ((hH.ker_b w hw.2).1 hwV)
    · exact hW0a w hw ((hH.ker_a w hw.2).1 hwV₂)
  obtain ⟨w₀, hw₀W, hw₀Z⟩ := Set.not_subset.1 hWZ
  have haw₀ : a w₀ ≠ 0 := fun ha => hw₀Z (hW0a w₀ hw₀W ha)
  have hbw₀ : b w₀ ≠ 0 := fun hb => hw₀Z (hW0b w₀ hw₀W hb)
  have hCJW : ∀ j ∈ J, (∀ w ∈ W, j * w = w * j) → j ∈ Z := by
    intro j hj hjW
    have hc0 : ∀ w ∈ W, a j * b w + a w * b j = 0 := by
      intro w hw
      have h1 := hH.comm j hj w hw.2
      rw [commutatorElement_eq_one_iff_mul_comm.2 (hjW w hw), hH.c_one] at h1
      exact h1.symm
    have haj : a j = 0 := by
      by_contra haj
      have hcard : 7 < Nat.card (GaloisField 2 e) := by
        rw [hq]
        calc 7 < 2 ^ 3 := by norm_num
          _ ≤ 2 ^ e := Nat.pow_le_pow_right (by norm_num) he3
      obtain ⟨t, ht0, ht6⟩ := exists_pow_six_ne_one hcard
      obtain ⟨w', hw', ha', hb'⟩ := hD t ht0 w₀ hw₀W
      have e0 := hc0 w₀ hw₀W
      have e1 := hc0 w' hw'
      rw [ha', hb'] at e1
      have ht3 : t ^ 3 ≠ 0 := pow_ne_zero 3 ht0
      have hinv : t ^ 3 * (t ^ 3)⁻¹ = 1 := mul_inv_cancel₀ ht3
      have key : a j * b w₀ * (t ^ 6 + 1) = 0 := by
        linear_combination t ^ 3 * e1 - e0 - (a w₀ * b j) * hinv + (a j * b w₀) * h2F
      rcases mul_eq_zero.1 key with h0 | h0
      · exact mul_ne_zero haj hbw₀ h0
      · exact ht6 (by linear_combination h0 - h2F)
    have hbj : b j = 0 := by
      have := hc0 w₀ hw₀W
      rw [haj, zero_mul, zero_add] at this
      exact (mul_eq_zero.1 this).resolve_left haw₀
    exact hH.mem_Z hinf hj haj hbj
  have hQT : ∀ q ∈ Q, q ∈ T → q ∈ J := by
    intro q hq hqT
    by_contra hqJ
    obtain ⟨⟨v, hv, hv'⟩, -⟩ := h.field.fixZ q hqT hqJ
    apply hv'
    have h1 := hcomm q hq v (h.base.V_le_J hv)
    have h2 : ⁅q, v⁆ ∈ V := by
      have : ⁅q, v⁆ = (q * v * q⁻¹) * v⁻¹ := by simp [commutatorElement_def, mul_assoc]
      rw [this]
      refine V.mul_mem ?_ (V.inv_mem hv)
      rw [← (h.base.T_norm q hqT).1]
      exact mul_mem_cj q hv
    exact hW0b _ h1 ((hH.ker_b _ h1.2).1 h2)
  obtain ⟨c₀, hc₀C, hc₀N⟩ : ∃ g ∈ C, g ∉ Subgroup.normalizer (Z : Set G) := by
    by_contra hcon
    push Not at hcon
    have hCJ : C ≤ Subgroup.normalizer (J : Set G) := fun g hg => h.normalizer_Z_le (hcon g hg)
    have hJQ : J ≤ Q := CFSG.LieType.BorelTits.le_pCoreOf_of_le_normalizer 2 hJC hCJ hJp
    obtain ⟨v, hvJ, hav, hbv⟩ := hH.surj_ab 1 0
    have := h₁ _ ⟨v, ⟨hJQ hvJ, hvJ⟩, hav, hbv⟩
    exact one_ne_zero this
  set Y := cj c₀ Z with hY
  have hYne : Y ≠ Z := fun hYZ => hc₀N (mem_normalizer_of_cj hYZ)
  have hYQ : Y ≤ Q := fun y hy => by
    obtain ⟨z', hz', rfl⟩ := Subgroup.mem_map.1 hy
    exact hQn c₀ hc₀C z' (hZW hz').1
  have hYel : ElemAb2 Y :=
    elemAb2_cj (CFSG.CGT.PushingUpLit.A78Sp4.ElemAb2.mono h.base.elem_V h.base.Z_le_V) c₀
  have hYT : ∀ y ∈ Y, y ∈ T → y ∈ Z := fun y hy hyT =>
    hinvW y ⟨hYQ hy, hQT y (hYQ hy) hyT⟩ (hYel y hy y hy).2
  obtain ⟨y₀, hy₀Y, hy₀T⟩ : ∃ y ∈ Y, y ∉ T := by
    by_contra hcon
    push Not at hcon
    apply hYne
    refine Subgroup.eq_of_le_of_card_ge (fun y hy => hYT y hy (hcon y hy)) ?_
    rw [hY, card_cj]
  have hy₀S : y₀ ∈ S := hQS (hYQ hy₀Y)
  have hcardYZ : 2 ^ e ≤ 2 * Nat.card ↥(Y ⊓ Z) := by
    classical
    let f : Y → ↥(Y ⊓ Z) × Bool := fun y =>
      if hyT : (y : G) ∈ T then (⟨(y : G), y.2, hYT _ y.2 hyT⟩, false)
      else (⟨y₀⁻¹ * y, Y.mul_mem (Y.inv_mem hy₀Y) y.2, hYT _ (Y.mul_mem (Y.inv_mem hy₀Y) y.2)
        (h.base.inv_mul_mem_T hy₀S (hQS (hYQ y.2)) hy₀T hyT)⟩, true)
    have hinj : Function.Injective f := by
      intro y y' hyy
      simp only [f] at hyy
      by_cases hy : (y : G) ∈ T <;> by_cases hy' : (y' : G) ∈ T
      · simp only [hy, hy', ↓reduceDIte] at hyy
        have h3 := congrArg (fun p : ↥(Y ⊓ Z) => (p : G)) (Prod.mk.inj hyy).1
        exact Subtype.ext h3
      · simp only [hy, hy', ↓reduceDIte] at hyy
        exact absurd (Prod.mk.inj hyy).2 (by decide)
      · simp only [hy, hy', ↓reduceDIte] at hyy
        exact absurd (Prod.mk.inj hyy).2 (by decide)
      · simp only [hy, hy', ↓reduceDIte] at hyy
        have h3 := congrArg (fun p : ↥(Y ⊓ Z) => (p : G)) (Prod.mk.inj hyy).1
        exact Subtype.ext (mul_left_cancel h3)
    have := Nat.card_le_card_of_injective f hinj
    rw [Nat.card_prod, Nat.card_eq_fintype_card (α := Bool), Fintype.card_bool] at this
    rw [hY, card_cj, h.base.card_Z] at this
    linarith
  have hy₀2 : y₀ * y₀ = 1 := (hYel y₀ hy₀Y y₀ hy₀Y).2
  have hy₀Z : ∀ z' ∈ Z, y₀ * z' = z' * y₀ := by
    rcases h.field.types y₀ hy₀S hy₀T hy₀2 with hJy | ⟨-, hle⟩
    · intro z' hz'
      have : z' ∈ J ⊓ Subgroup.centralizer ({y₀} : Set G) := by rw [hJy]; exact hz'
      exact (Subgroup.mem_centralizer_singleton_iff.1 this.2).symm
    · exfalso
      have hle2 : Nat.card ↥(Y ⊓ Z) ≤ Nat.card ↥(Z ⊓ Subgroup.centralizer ({y₀} : Set G)) := by
        exact Subgroup.card_le_of_le fun y hy =>
          ⟨hy.2, Subgroup.mem_centralizer_singleton_iff.2 (hYel y hy.1 y₀ hy₀Y).1⟩
      have h3 : 2 ^ e ≤ 2 * 2 ^ (e / 2) := by linarith
      have h4 : 2 ^ e ≤ 2 ^ (e / 2 + 1) := by rw [pow_succ]; linarith
      have h5 := (Nat.pow_le_pow_iff_right (by norm_num : 1 < 2)).1 h4
      omega
  have hZcent : ∀ q ∈ Q, ∀ z' ∈ Z, q * z' = z' * q := by
    intro q hq z' hz'
    by_cases hqT : q ∈ T
    · exact (hH.central hinf hZJ h.base.comm_mem hz' (hQT q hq hqT)).symm
    · have hm : y₀⁻¹ * q ∈ T := h.base.inv_mul_mem_T hy₀S (hQS hq) hy₀T hqT
      have hmJ : y₀⁻¹ * q ∈ J := hQT _ (Q.mul_mem (Q.inv_mem (hYQ hy₀Y)) hq) hm
      have h1 := hH.central hinf hZJ h.base.comm_mem hz' hmJ
      have e1 : q = y₀ * (y₀⁻¹ * q) := by group
      rw [e1, mul_assoc, ← h1, ← mul_assoc, hy₀Z z' hz', mul_assoc]
  let E : Subgroup G :=
    { carrier := {x | x ∈ qCenter Q ∧ x * x = 1}
      one_mem' := ⟨(qCenter Q).one_mem, by simp⟩
      mul_mem' := by
        rintro x y ⟨hx, hxx⟩ ⟨hy, hyy⟩
        refine ⟨(qCenter Q).mul_mem hx hy, ?_⟩
        have hxy : y * x = x * y := ((mem_qCenter.1 hy).2 x (mem_qCenter.1 hx).1).symm
        calc x * y * (x * y) = x * (y * x) * y := by group
          _ = x * (x * y) * y := by rw [hxy]
          _ = (x * x) * (y * y) := by group
          _ = 1 := by rw [hxx, hyy, one_mul]
      inv_mem' := by
        rintro x ⟨hx, hxx⟩
        have hxi : x⁻¹ = x := inv_eq_of_mul_eq_one_right hxx
        show x⁻¹ ∈ qCenter Q ∧ x⁻¹ * x⁻¹ = 1
        rw [hxi]
        exact ⟨hx, hxx⟩ }
  have hEC : ∀ g ∈ C, ∀ x ∈ E, g * x * g⁻¹ ∈ E := by
    rintro g hg x ⟨hx, hxx⟩
    refine ⟨qCenter_conj_mem_of hQn hg hx, ?_⟩
    calc g * x * g⁻¹ * (g * x * g⁻¹) = g * (x * x) * g⁻¹ := by group
      _ = 1 := by rw [hxx]; group
  have hZE : Z ≤ E := by
    intro z' hz'
    refine ⟨mem_qCenter.2 ⟨(hZW hz').1, fun q hq => hZcent q hq z' hz'⟩, ?_⟩
    exact (h.base.elem_V z' (h.base.Z_le_V hz') z' (h.base.Z_le_V hz')).2
  have hET : ∀ x ∈ E, x ∈ T → x ∈ Z := by
    rintro x ⟨hx, -⟩ hxT
    have hx' := mem_qCenter.1 hx
    exact hCJW x (hQT x hx'.1 hxT) fun w hw => (hx'.2 w hw.1).symm
  obtain ⟨e₀, he₀E, he₀Z⟩ : ∃ x ∈ E, x ∉ Z := by
    by_contra hcon
    push Not at hcon
    apply hc₀N
    exact mem_normalizer_of_conj_mem fun x hx => hcon _ (hEC c₀ hc₀C x (hZE hx))
  have he₀T : e₀ ∉ T := fun hT' => he₀Z (hET e₀ he₀E hT')
  have he₀S : e₀ ∈ S := hQS (mem_qCenter.1 he₀E.1).1
  apply he₀T
  refine h.base.J_le (h.base.cent_S e₀ he₀S fun j hj => ?_)
  have h1 : ⁅e₀, j⁆ ∈ E := by
    have : ⁅e₀, j⁆ = e₀ * (j * e₀⁻¹ * j⁻¹) := by simp [commutatorElement_def, mul_assoc]
    rw [this]
    exact E.mul_mem he₀E (hEC j (hJC hj) _ (E.inv_mem he₀E))
  have h2 : ⁅e₀, j⁆ ∈ J := by
    have : ⁅e₀, j⁆ = (e₀ * j * e₀⁻¹) * j⁻¹ := by simp [commutatorElement_def, mul_assoc]
    rw [this]
    exact J.mul_mem (h.base.conj_J he₀S hj) (J.inv_mem hj)
  exact hET _ h1 (h.base.J_le h2)

theorem T2Loc.centralizer_le (h : T2Loc G L L₂ V V₂ Z J T S M M₂ e) {z : G} (hz : z ∈ Z)
    (hz1 : z ≠ 1) : Subgroup.centralizer ({z} : Set G) ≤ Subgroup.normalizer (J : Set G) := by
  obtain ⟨a, b, c, hH, hT⟩ := h.coords
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨z₀, ⟨hz₀, hz₀1⟩, hfix⟩ := CFSG.CGT.PushingUpLit.A78Sp4.exists_fixed_conj_of_not_dvd
    (p := 2) h.base.isPGroup_S (X := {x : G | x ∈ Z ∧ x ≠ 1})
    (fun s hs x hx => ⟨h.base.conj_Z hs hx.1, fun h1 => hx.2 (by
      have : x = s⁻¹ * (s * x * s⁻¹) * s := by group
      rw [this, h1]; group)⟩) (by
      have hX : {x : G | x ∈ Z ∧ x ≠ 1} = (Z : Set G) \ {1} := by
        ext x; simp
      rw [hX, Nat.card_coe_set_eq, Set.ncard_sdiff_singleton_of_mem Z.one_mem,
        ← Nat.card_coe_set_eq, SetLike.coe_sort_coe, h.base.card_Z]
      have h2 : 2 ∣ 2 ^ e := dvd_pow_self 2 (by have := h.base.two_le; omega)
      have h1 : 1 ≤ 2 ^ e := Nat.one_le_two_pow
      omega)
  have hcen : ∀ s ∈ S, s * z₀ = z₀ * s := fun s hs => by
    have := hfix s hs
    calc s * z₀ = s * z₀ * s⁻¹ * s := by group
      _ = z₀ * s := by rw [this]
  have hJQ := h.J_le_O2_cent hz₀ hz₀1 hcen
  have hC₀ : Subgroup.centralizer ({z₀} : Set G) ≤ Subgroup.normalizer (J : Set G) := by
    have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
    set C := Subgroup.centralizer ({z₀} : Set G)
    have hSC : S ≤ C := fun s hs => Subgroup.mem_centralizer_singleton_iff.2 (hcen s hs)
    have hQS : CFSG.Open.pCoreOf 2 C ≤ S :=
      pCoreOf_le_of_isSylowOf (h.base.sylow.of_le hSC le_top)
    intro g hg
    exact h.base.mem_normalizer_J_of_le hQS hJQ fun q hq =>
      (Subgroup.mem_normalizer_iff.1 (CFSG.LieType.BorelTits.le_normalizer_pCoreOf 2 C hg) q).1 hq
  have hc0 : ∀ x ∈ Z, x ≠ 1 → c x ≠ 0 := fun x hx hx1 hcx =>
    hx1 (hH.inj_c x hx 1 Z.one_mem (by rw [hcx, hH.c_one]))
  obtain ⟨x, -, hxJ, -, hxZ⟩ := hT.torus₁ (c z / c z₀) (div_ne_zero (hc0 z hz hz1)
    (hc0 z₀ hz₀ hz₀1))
  have hxz : x * z₀ * x⁻¹ = z := by
    refine hH.inj_c _ (hxZ z₀ hz₀).1 z hz ?_
    rw [(hxZ z₀ hz₀).2]
    field_simp [hc0 z₀ hz₀ hz₀1]
  have hxN : x ∈ Subgroup.normalizer (J : Set G) := mem_normalizer_of_conj_mem hxJ
  intro g hg
  have hg' : x⁻¹ * g * x ∈ Subgroup.centralizer ({z₀} : Set G) := by
    rw [Subgroup.mem_centralizer_singleton_iff] at hg ⊢
    have h1 : z₀ = x⁻¹ * z * x := by rw [← hxz]; group
    rw [h1]
    calc x⁻¹ * g * x * (x⁻¹ * z * x) = x⁻¹ * (g * z) * x := by group
      _ = x⁻¹ * (z * g) * x := by rw [hg]
      _ = x⁻¹ * z * x * (x⁻¹ * g * x) := by group
  have h2 := hC₀ hg'
  have e1 : g = x * (x⁻¹ * g * x) * x⁻¹ := by group
  rw [e1]
  exact Subgroup.mul_mem _ (Subgroup.mul_mem _ hxN h2) (Subgroup.inv_mem _ hxN)

theorem T2Base.cj_J_eq_of_le (h : T2Base G V V₂ Z J T S M M₂ e) {g : G} (hle : cj g J ≤ S) :
    cj g J = J := by
  have hcV : ∀ U : Subgroup G, ElemAb2 U → Nat.card U = 2 ^ (2 * e) → U ≤ J →
      cj g U = V ∨ cj g U = V₂ := fun U hU hUc hUJ =>
    h.A_S _ ((cj_mono g hUJ).trans hle) (elemAb2_cj hU g) ((card_cj g U).trans hUc)
  have h1 := hcV V h.elem_V h.card_V h.V_le_J
  have h2 := hcV V₂ h.elem_V₂ h.card_V₂ h.V₂_le_J
  have hne : cj g V ≠ cj g V₂ := fun heq =>
    h.V_ne (Subgroup.map_injective (f := (MulAut.conj g).toMonoidHom) (MulAut.conj g).injective heq)
  rw [← h.sup, cj_sup_eq]
  rcases h1 with h1 | h1 <;> rcases h2 with h2 | h2
  · exact absurd (h1.trans h2.symm) hne
  · rw [h1, h2]
  · rw [h1, h2, sup_comm]
  · exact absurd (h1.trans h2.symm) hne

theorem T2Loc.ti (h : T2Loc G L L₂ V V₂ Z J T S M M₂ e) (g : G) (hne : Z ⊓ cj g Z ≠ ⊥) :
    cj g Z = Z := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨a, b, c, hH, -⟩ := h.coords
  have hcentZ : ∀ {x : G}, x ∈ Z → ∀ {j : G}, j ∈ J → x * j = j * x := fun hx _ hj =>
    hH.central h.base.inf h.base.Z_le_J h.base.comm_mem hx hj
  obtain ⟨y, ⟨hyZ, hyg⟩, hy1⟩ : ∃ y ∈ Z ⊓ cj g Z, y ≠ 1 := by
    by_contra hcon
    push Not at hcon
    exact hne ((Subgroup.eq_bot_iff_forall _).2 hcon)
  replace hyg : g⁻¹ * y * g ∈ Z := (mem_cj_iff g Z y).1 hyg
  have hy'1 : g⁻¹ * y * g ≠ 1 := fun h1 => hy1 (by
    have : y = g * (g⁻¹ * y * g) * g⁻¹ := by group
    rw [this, h1]; group)
  set Cy := Subgroup.centralizer ({y} : Set G)
  have hN1 : Cy ≤ Subgroup.normalizer (J : Set G) := h.centralizer_le hyZ hy1
  have hN2 : Cy ≤ Subgroup.normalizer (cj g J : Set G) := by
    intro x hx
    have hx' : g⁻¹ * x * g ∈ Subgroup.centralizer ({g⁻¹ * y * g} : Set G) := by
      rw [Subgroup.mem_centralizer_singleton_iff] at hx ⊢
      calc g⁻¹ * x * g * (g⁻¹ * y * g) = g⁻¹ * (x * y) * g := by group
        _ = g⁻¹ * (y * x) * g := by rw [hx]
        _ = g⁻¹ * y * g * (g⁻¹ * x * g) := by group
    have hn := h.centralizer_le hyg hy'1 hx'
    refine mem_normalizer_of_conj_mem fun w hw => ?_
    rw [mem_cj_iff] at hw ⊢
    have e1 : g⁻¹ * (x * w * x⁻¹) * g = (g⁻¹ * x * g) * (g⁻¹ * w * g) * (g⁻¹ * x * g)⁻¹ := by group
    rw [e1]
    exact (Subgroup.mem_normalizer_iff.1 hn _).1 hw
  have hJp : IsPGroup 2 J := h.base.isPGroup_S.to_le h.base.J_le_S
  have hJgp : IsPGroup 2 (cj g J) := hJp.map _
  have hJy : J ≤ Cy := fun j hj => Subgroup.mem_centralizer_singleton_iff.2
    (hcentZ hyZ hj).symm
  have hJgy : cj g J ≤ Cy := by
    intro j hj
    rw [mem_cj_iff] at hj
    have h1 := hcentZ hyg hj
    rw [Subgroup.mem_centralizer_singleton_iff]
    have e1 : j = g * (g⁻¹ * j * g) * g⁻¹ := by group
    have e2 : y = g * (g⁻¹ * y * g) * g⁻¹ := by group
    rw [e1, e2]
    calc g * (g⁻¹ * j * g) * g⁻¹ * (g * (g⁻¹ * y * g) * g⁻¹)
        = g * ((g⁻¹ * j * g) * (g⁻¹ * y * g)) * g⁻¹ := by group
      _ = g * ((g⁻¹ * y * g) * (g⁻¹ * j * g)) * g⁻¹ := by rw [h1]
      _ = g * (g⁻¹ * y * g) * g⁻¹ * (g * (g⁻¹ * j * g) * g⁻¹) := by group
  have hP : IsPGroup 2 (J ⊔ cj g J : Subgroup G) := hJp.to_sup_of_normal_right' hJgp
    (hJy.trans hN2)
  obtain ⟨k, -, hk⟩ := exists_conj_le_of_isSylowOf h.base.sylow le_top hP
  have hk1 : cj k J = J := h.base.cj_J_eq_of_le ((cj_mono k le_sup_left).trans hk)
  have hk2 : cj (k * g) J = J := by
    refine h.base.cj_J_eq_of_le ?_
    rw [← cj_cj]
    exact (cj_mono k le_sup_right).trans hk
  have hgJ : cj g J = J := by
    have h3 : cj k (cj g J) = cj k J := by rw [cj_cj, hk2, hk1]
    exact Subgroup.map_injective (f := (MulAut.conj k).toMonoidHom) (MulAut.conj k).injective h3
  have hgN : g ∈ Subgroup.normalizer (Z : Set G) := h.normalizer_J_le (mem_normalizer_of_cj hgJ)
  exact CFSG.CGT.PushingUpLit.A78Sp4.cj_eq_of_mem_normalizer_set hgN

end CFSG.CGT.PushingUpLit.A78T2
