module

public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.Lin2.InPartI1
public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.Lin2.InCount

public section

namespace CFSG.QuasithinUnique.Lin2

open CFSG.Open CFSG.Quasithin

section Generic

variable {G : Type*} [Group G]

theorem mem_of_sq_mem_of_odd {X : Subgroup G} {d : G} (hodd : Odd (orderOf d))
    (h : d * d ∈ X) : d ∈ X := by
  obtain ⟨j, hj⟩ := hodd
  have hd : d ^ (2 * j + 1) = 1 := by rw [← hj]; exact pow_orderOf_eq_one d
  have e : d = (d * d) ^ (j + 1) := by
    have : (d * d) ^ (j + 1) = d ^ (2 * (j + 1)) := by rw [← pow_two, ← pow_mul]
    rw [this]
    have h2 : 2 * (j + 1) = (2 * j + 1) + 1 := by ring
    rw [h2, pow_succ, hd, one_mul]
  rw [e]
  exact Subgroup.pow_mem X h (j + 1)

theorem mem_normalizer_inf_centralizer {R L' : Subgroup G} {d : G}
    (hR : d ∈ Subgroup.normalizer (R : Set G)) (hL : d ∈ Subgroup.normalizer (L' : Set G)) :
    d ∈ Subgroup.normalizer ((R ⊓ Subgroup.centralizer (L' : Set G) : Subgroup G) : Set G) := by
  rw [← conjR_eq_self_iff, conjR_inf, conjR_eq_of_mem_normalizer hR, ← conjR_centralizer,
    conjR_eq_of_mem_normalizer hL]

theorem mem_normalizer_blockZ_of {L : Subgroup G} {a : G}
    (ha : a ∈ Subgroup.normalizer (L : Set G)) : a ∈ Subgroup.normalizer (blockZ L : Set G) := by
  unfold blockZ
  rw [← conjR_eq_self_iff, conjR_inf, ← conjR_centralizer, conjR_eq_of_mem_normalizer ha,
    conjR_eq_self_iff.2 (mem_normalizer_blockU_of ha)]

theorem isMaxElemAbelian_conjR_of_normalizer {S R A : Subgroup G} (hA : IsMaxElemAbelian S A)
    (hRS : R ≤ S) (hAR : A ≤ R) {d : G} (hd : d ∈ Subgroup.normalizer (R : Set G)) :
    IsMaxElemAbelian S (conjR A d) := by
  refine ⟨?_, (isElemAbelian_conjR_iff A d).2 hA.2.1, ?_⟩
  · calc conjR A d ≤ conjR R d := conjR_mono hAR d
      _ = R := conjR_eq_of_mem_normalizer hd
      _ ≤ S := hRS
  · intro B hB hBe
    rw [card_conjR]
    exact hA.2.2 B hB hBe

end Generic

variable {G : Type} [Group G] [Finite G] {T M H S L D : Subgroup G} {n : ℕ}

section Elements

theorem orderOf_odd_of_mem (h : Lin2Cfg G T M H S L n D) {d : G} (hd : d ∈ D) :
    Odd (orderOf d) := by
  have hord : orderOf d ∣ Nat.card D := by
    have := orderOf_dvd_natCard (⟨d, hd⟩ : D)
    rwa [Subgroup.orderOf_mk] at this
  exact Odd.of_dvd_nat h.hall.2.1 hord

end Elements

section XFacts

variable (h : Lin2Cfg G T M H S L n D) (dat : Lin2Data T M H S L n)
include h dat

theorem Lin2Data.x_normalizer_S {x : G} (hx : x ∈ T) : x ∈ Subgroup.normalizer (S : Set G) :=
  le_normalizer_of_relIndex_two h.S_le_T dat.index_two hx

theorem Lin2Data.x_normalizer_R {x : G} (hx : x ∈ T) :
    x ∈ Subgroup.normalizer (thompsonJ S : Set G) :=
  conjR_eq_self_iff.1 (thompsonJ_normalized (dat.x_normalizer_S h hx))

theorem Lin2Data.Q_ne_conj {x : G} (hx : x ∈ T) (hxS : x ∉ S) :
    conjR (pCoreOf 2 H) x ≠ pCoreOf 2 H := by
  intro hQ
  have hR : thompsonJ S ≤ pCoreOf 2 H := by
    rw [dat.R_eq x hx hxS]
    refine sup_le (sup_le dat.D₀_le_Q dat.U_le_Q) ?_
    calc conjR (blockU L) x ≤ conjR (pCoreOf 2 H) x := conjR_mono dat.U_le_Q x
      _ = pCoreOf 2 H := hQ
  have h1 : (pCoreOf 2 H).relIndex (thompsonJ S) = 1 := Subgroup.relIndex_eq_one.2 hR
  rw [dat.RQ_index] at h1
  have h2 : 1 < 2 ^ n := Nat.one_lt_two_pow (by have := h.one_lt; omega)
  omega

end XFacts

omit [Finite G] in
theorem Lin2Data.x_sq_mem (dat : Lin2Data T M H S L n) {x : G} (hx : x ∈ T) : x * x ∈ S := by
  have := sq_mem_of_relIndex_two dat.index_two hx
  rwa [pow_two] at this

section DQ

variable (h : Lin2Cfg G T M H S L n D) (dat : Lin2Data T M H S L n)
include h dat

theorem Lin2Data.D_normalizes_Q {x : G} (hx : x ∈ T) (hxS : x ∉ S) {d : G} (hd : d ∈ D) :
    d ∈ Subgroup.normalizer (pCoreOf 2 H : Set G) ∧
      d ∈ Subgroup.normalizer ((conjR (pCoreOf 2 H) x : Subgroup G) : Set G) := by
  have hdR : d ∈ Subgroup.normalizer (thompsonJ S : Set G) := dat.D_le_normalizer_R h hd
  have hRS : thompsonJ S ≤ S := thompsonJ_le_self S
  have hQR : pCoreOf 2 H ≤ thompsonJ S := dat.Q_le_R h
  have hQxR : conjR (pCoreOf 2 H) x ≤ thompsonJ S := by
    calc conjR (pCoreOf 2 H) x ≤ conjR (thompsonJ S) x := conjR_mono hQR x
      _ = thompsonJ S := conjR_eq_of_mem_normalizer (dat.x_normalizer_R h hx)
  have hQmax : IsMaxElemAbelian S (pCoreOf 2 H) := dat.Q_max
  have hQxmax : IsMaxElemAbelian S (conjR (pCoreOf 2 H) x) :=
    (dat.A_eq x hx hxS _).2 (Or.inr rfl)
  have hne := dat.Q_ne_conj h hx hxS
  have hA : ∀ B : Subgroup G, (B = pCoreOf 2 H ∨ B = conjR (pCoreOf 2 H) x) →
      conjR B d = pCoreOf 2 H ∨ conjR B d = conjR (pCoreOf 2 H) x := by
    intro B hB
    rcases hB with rfl | rfl
    · exact (dat.A_eq x hx hxS _).1
        (isMaxElemAbelian_conjR_of_normalizer hQmax hRS hQR hdR)
    · exact (dat.A_eq x hx hxS _).1
        (isMaxElemAbelian_conjR_of_normalizer hQxmax hRS hQxR hdR)
  have hodd := orderOf_odd_of_mem h hd
  have hdQ : d ∈ Subgroup.normalizer (pCoreOf 2 H : Set G) := by
    by_contra hdQ
    have h1 : conjR (pCoreOf 2 H) d ≠ pCoreOf 2 H := fun e => hdQ (conjR_eq_self_iff.1 e)
    have h1' : conjR (pCoreOf 2 H) d = conjR (pCoreOf 2 H) x :=
      (hA _ (Or.inl rfl)).resolve_left h1
    have e2 : conjR (conjR (pCoreOf 2 H) x) d = conjR (pCoreOf 2 H) (d * d) := by
      rw [← h1', conjR_conjR]
    rcases hA _ (Or.inr rfl) with h2 | h2
    · apply hdQ
      refine mem_of_sq_mem_of_odd hodd ?_
      rw [← conjR_eq_self_iff, ← e2]
      exact h2
    · apply h1
      have h3 : conjR (conjR (pCoreOf 2 H) d) d = conjR (pCoreOf 2 H) d := by
        rw [h1']; exact h2
      have h4 := congrArg (fun X => conjR X d⁻¹) h3
      simpa only [conjR_conjR_inv] using h4
  refine ⟨hdQ, ?_⟩
  have hcd : conjR (pCoreOf 2 H) d = pCoreOf 2 H := conjR_eq_self_iff.2 hdQ
  by_contra hdQx
  have h1 : conjR (conjR (pCoreOf 2 H) x) d ≠ conjR (pCoreOf 2 H) x :=
    fun e => hdQx (conjR_eq_self_iff.1 e)
  have h2 : conjR (conjR (pCoreOf 2 H) x) d = pCoreOf 2 H :=
    (hA _ (Or.inr rfl)).resolve_right h1
  have h3 := congrArg (fun X => conjR X d⁻¹) h2
  simp only [conjR_conjR_inv] at h3
  have hdi : conjR (pCoreOf 2 H) d⁻¹ = pCoreOf 2 H :=
    conjR_eq_self_iff.2 (Subgroup.inv_mem _ hdQ)
  rw [hdi] at h3
  exact hne h3

end DQ

section Conj

variable (h : Lin2Cfg G T M H S L n D) (dat : Lin2Data T M H S L n)
include h dat

theorem Lin2Data.D_normalizes_conjL {x : G} (hx : x ∈ T) (hxS : x ∉ S) :
    D ≤ Subgroup.normalizer ((conjR L x : Subgroup G) : Set G) := by
  intro d hd
  have h1 := (dat.D_normalizes_Q h hx hxS hd).2
  rw [conjR_normalizer] at h1
  rw [conjR_normalizer]
  exact conjR_mono (X := Subgroup.normalizer (pCoreOf 2 H : Set G))
    (Y := Subgroup.normalizer (L : Set G)) dat.norm_Q x h1

theorem Lin2Data.conjR_D_le_normalizer_L {x : G} (hx : x ∈ T) (hxS : x ∉ S) :
    conjR D x ≤ Subgroup.normalizer (L : Set G) := by
  intro y hy
  have hy' : x * y * x⁻¹ ∈ D := mem_conjR.1 hy
  have h1 := dat.D_normalizes_conjL h hx hxS hy'
  rw [conjR_normalizer, mem_conjR] at h1
  have hxx : x * x ∈ S := dat.x_sq_mem hx
  have hN : x * x ∈ Subgroup.normalizer (L : Set G) := h.S_le_normalizer hxx
  have e : y = (x * x)⁻¹ * (x * (x * y * x⁻¹) * x⁻¹) * (x * x) := by group
  rw [e]
  exact Subgroup.mul_mem _ (Subgroup.mul_mem _ (Subgroup.inv_mem _ hN) h1) hN

theorem Lin2Data.conjR_D_le_normalizer_R {x : G} (hx : x ∈ T) :
    conjR D x ≤ Subgroup.normalizer (thompsonJ S : Set G) := by
  intro y hy
  have hy' : x * y * x⁻¹ ∈ D := mem_conjR.1 hy
  have h1 := dat.D_le_normalizer_R h hy'
  have hxR := dat.x_normalizer_R h hx
  have e : y = x⁻¹ * (x * y * x⁻¹) * x := by group
  rw [e]
  exact Subgroup.mul_mem _ (Subgroup.mul_mem _ (Subgroup.inv_mem _ hxR) h1) hxR

theorem Lin2Data.D₀_eq_inf_R : blockD S L = thompsonJ S ⊓ Subgroup.centralizer (L : Set G) := by
  apply le_antisymm
  · exact le_inf (dat.D₀_le_R h) (by rw [dat.D₀_eq]; exact inf_le_right)
  · rw [dat.D₀_eq]
    exact inf_le_inf_right _ (thompsonJ_le_self S)

theorem Lin2Data.conjR_D₀ {x : G} (hx : x ∈ T) :
    conjR (blockD S L) x =
      thompsonJ S ⊓ Subgroup.centralizer ((conjR L x : Subgroup G) : Set G) := by
  rw [dat.D₀_eq_inf_R h, conjR_inf, conjR_eq_of_mem_normalizer (dat.x_normalizer_R h hx),
    conjR_centralizer]

theorem Lin2Data.mem_normalizer_D₀ {a : G} (haR : a ∈ Subgroup.normalizer (thompsonJ S : Set G))
    (haL : a ∈ Subgroup.normalizer (L : Set G)) :
    a ∈ Subgroup.normalizer (blockD S L : Set G) := by
  rw [dat.D₀_eq_inf_R h]
  exact mem_normalizer_inf_centralizer haR haL

theorem Lin2Data.conjR_D₀_le_P {x : G} (hx : x ∈ T) (hxS : x ∉ S) :
    conjR (blockD S L) x ≤ S ⊓ L := by
  have hDne : D ≠ ⊥ := by
    intro hD
    have h1 := h.card_D
    rw [hD, Subgroup.card_bot] at h1
    have h4 : 4 ≤ 2 ^ n := h.four_le_two_pow
    omega
  obtain ⟨δ, hδ⟩ := (Subgroup.ne_bot_iff_exists_ne_one).1 hDne
  have hδD : (δ : G) ∈ D := δ.2
  have hδ1 : (δ : G) ≠ 1 := fun e => hδ (Subtype.ext e)
  have hδL : (δ : G) ∈ L := h.D_le_L hδD
  have hδR := dat.D_le_normalizer_R h hδD
  have hXeq := dat.conjR_D₀ h hx
  have hXe : IsElemAbelian 2 (conjR (blockD S L) x) :=
    (isElemAbelian_conjR_iff _ _).2 dat.D₀_elem
  have hXcomm : ∀ a ∈ conjR (blockD S L) x, ∀ b ∈ conjR (blockD S L) x, a * b = b * a :=
    fun a ha b hb => IsElemAbelian.comm hXe ha hb
  have hXR : conjR (blockD S L) x ≤ thompsonJ S := by rw [hXeq]; exact inf_le_left
  have hδnorm : ∀ z ∈ conjR (blockD S L) x, (δ : G) * z * (δ : G)⁻¹ ∈ conjR (blockD S L) x := by
    intro z hz
    have hn : (δ : G) ∈ Subgroup.normalizer ((conjR (blockD S L) x : Subgroup G) : Set G) := by
      rw [hXeq]
      exact mem_normalizer_inf_centralizer hδR (dat.D_normalizes_conjL h hx hxS hδD)
    exact (Subgroup.mem_normalizer_iff.1 hn z).1 hz
  have hfix : ∀ z ∈ conjR (blockD S L) x, (δ : G) * z * (δ : G)⁻¹ = z → z = 1 := by
    intro z hz hc
    have hz' : (δ : G) * z = z * δ := by
      calc (δ : G) * z = ((δ : G) * z * (δ : G)⁻¹) * δ := by group
        _ = z * δ := by rw [hc]
    have hzD₀ : z ∈ blockD S L := dat.centralizer_R h hδD hδ1 (hXR hz) hz'
    have hmem : z ∈ blockD S L ⊓ conjR (blockD S L) x := ⟨hzD₀, hz⟩
    rw [dat.D₀_inf x hx hxS, Subgroup.mem_bot] at hmem
    exact hmem
  intro y hy
  obtain ⟨z, hz, rfl⟩ := exists_eq_commutator_of_fixed_trivial hXcomm hδnorm hfix hy
  have hzR : z ∈ thompsonJ S := hXR hz
  have h1 : (δ : G) * z * (δ : G)⁻¹ ∈ thompsonJ S :=
    (Subgroup.mem_normalizer_iff.1 hδR z).1 hzR
  have h2 : z * (δ : G)⁻¹ * z⁻¹ ∈ L :=
    (Subgroup.mem_normalizer_iff.1 (dat.R_norm hzR) (δ : G)⁻¹).1 (L.inv_mem hδL)
  have h3 : (δ : G) * z * (δ : G)⁻¹ * z⁻¹ = (δ : G) * (z * (δ : G)⁻¹ * z⁻¹) := by group
  rw [← dat.R_inf_L h]
  refine ⟨Subgroup.mul_mem _ h1 (Subgroup.inv_mem _ hzR), ?_⟩
  rw [h3]
  exact L.mul_mem hδL h2

end Conj

section Counting

variable (h : Lin2Cfg G T M H S L n D) (dat : Lin2Data T M H S L n)
include h dat

theorem Lin2Data.conjR_D_normalizes_D₀ {x : G} (hx : x ∈ T) (hxS : x ∉ S) {a : G}
    (ha : a ∈ conjR D x) : a ∈ Subgroup.normalizer (blockD S L : Set G) :=
  dat.mem_normalizer_D₀ h (dat.conjR_D_le_normalizer_R h hx ha)
    (dat.conjR_D_le_normalizer_L h hx hxS ha)

theorem Lin2Data.conjR_D_free {x : G} (hx : x ∈ T) (hxS : x ∉ S) {a : G} (ha : a ∈ conjR D x)
    (ha1 : a ≠ 1) {y : G} (hy : y ∈ blockD S L) (hay : a⁻¹ * y * a = y) : y = 1 := by
  obtain ⟨δ, hδ, rfl⟩ := mem_conjR_iff'.1 ha
  have hδ1 : δ ≠ 1 := by
    rintro rfl
    exact ha1 (by simp)
  have hxR := dat.x_normalizer_R h hx
  have hyR : y ∈ thompsonJ S := dat.D₀_le_R h hy
  have hy' : x * y * x⁻¹ ∈ thompsonJ S := (Subgroup.mem_normalizer_iff.1 hxR y).1 hyR
  have h8 : y * (x⁻¹ * δ * x) = (x⁻¹ * δ * x) * y := by
    calc y * (x⁻¹ * δ * x) = (x⁻¹ * δ * x) * ((x⁻¹ * δ * x)⁻¹ * y * (x⁻¹ * δ * x)) := by group
      _ = (x⁻¹ * δ * x) * y := by rw [hay]
  have hc : δ * (x * y * x⁻¹) = (x * y * x⁻¹) * δ := by
    calc δ * (x * y * x⁻¹) = x * ((x⁻¹ * δ * x) * y) * x⁻¹ := by group
      _ = x * (y * (x⁻¹ * δ * x)) * x⁻¹ := by rw [h8]
      _ = (x * y * x⁻¹) * δ := by group
  have hmem : x * y * x⁻¹ ∈ blockD S L := dat.centralizer_R h hδ hδ1 hy' hc
  have hyx : y ∈ conjR (blockD S L) x := mem_conjR.2 hmem
  have : y ∈ blockD S L ⊓ conjR (blockD S L) x := ⟨hy, hyx⟩
  rw [dat.D₀_inf x hx hxS, Subgroup.mem_bot] at this
  exact this

theorem Lin2Data.D₀_eq_bot_or_card : blockD S L = ⊥ ∨ Nat.card (blockD S L) = 2 ^ n := by
  by_cases hbot : blockD S L = ⊥
  · exact Or.inl hbot
  right
  obtain ⟨y, hy⟩ := (Subgroup.ne_bot_iff_exists_ne_one).1 hbot
  obtain ⟨x, hx, hxS⟩ := h.exists_mem_T_not_mem_S
  have hy1 : (y : G) ≠ 1 := fun e => hy (Subtype.ext e)
  have hle := card_add_one_le_of_free (A := conjR D x) (Y := blockD S L)
    (fun a ha y hy => by
      have hn := dat.conjR_D_normalizes_D₀ h hx hxS ha
      have := (Subgroup.mem_normalizer_iff.1 (Subgroup.inv_mem _ hn) y).1 hy
      simpa using this)
    (fun a ha ha1 y hy hay => dat.conjR_D_free h hx hxS ha ha1 hy hay) y.2 hy1
  rw [card_conjR, h.card_D] at hle
  have h1 : 1 ≤ 2 ^ n := Nat.one_le_two_pow
  have h2 := dat.D₀_bound
  omega

theorem Lin2Data.blockZ_eq_D₀ (hZ : blockZ L ≠ ⊥) :
    blockZ L = blockD S L ∧ Nat.card (blockD S L) = 2 ^ n := by
  have hD₀ : blockD S L ≠ ⊥ := fun e =>
    hZ (le_bot_iff.1 (e ▸ dat.Z_le_D₀ h))
  have hcard : Nat.card (blockD S L) = 2 ^ n := (dat.D₀_eq_bot_or_card h).resolve_left hD₀
  obtain ⟨z, hz⟩ := (Subgroup.ne_bot_iff_exists_ne_one).1 hZ
  obtain ⟨x, hx, hxS⟩ := h.exists_mem_T_not_mem_S
  have hz1 : (z : G) ≠ 1 := fun e => hz (Subtype.ext e)
  have hle := card_add_one_le_of_free (A := conjR D x) (Y := blockZ L)
    (fun a ha y hy => by
      have hn := mem_normalizer_blockZ_of (dat.conjR_D_le_normalizer_L h hx hxS ha)
      have := (Subgroup.mem_normalizer_iff.1 (Subgroup.inv_mem _ hn) y).1 hy
      simpa using this)
    (fun a ha ha1 y hy hay => dat.conjR_D_free h hx hxS ha ha1 (dat.Z_le_D₀ h hy) hay) z.2 hz1
  rw [card_conjR, h.card_D] at hle
  have h1 : 1 ≤ 2 ^ n := Nat.one_le_two_pow
  refine ⟨Subgroup.eq_of_le_of_card_ge (dat.Z_le_D₀ h) ?_, hcard⟩
  rw [hcard]
  omega

end Counting



end CFSG.QuasithinUnique.Lin2
