module

public import CFSG.Certificates.Kernel.G2Three.Sec1T3F13
public import CFSG.Certificates.Kernel.G2Three.Sec1T3CSound
public import CFSG.LocalAnalysis.OddStandard.HigherRank.G2Three.Sec1Proof.TabOps4

public section

namespace CFSG.KC.G2Three.Sec1T3

open CFSG.KD.G2Three.Sec1T3 CFSG.KC.Loop CFSG.OddStandard.HigherRank.G2Three.Sec1 Subgroup
open CFSG.OddStandard.HigherRank.G2Three.Sec1Proof (sGen)
open CFSG.Open (IsElemAbelian)
open scoped commutatorElement

variable {Γ : Type} [Group Γ] {elt : ℕ → Γ} {P C V Q : ℕ}

theorem f15a_two_bit (a b j : ℕ) :
    (Nat.lor (Nat.shiftLeft 1 a) (Nat.shiftLeft 1 b)).testBit j = true ↔ j = a ∨ j = b := by
  change (1 <<< a ||| 1 <<< b).testBit j = true ↔ _
  rw [Nat.testBit_or, Nat.one_shiftLeft, Nat.one_shiftLeft, Nat.testBit_two_pow,
    Nat.testBit_two_pow, Bool.or_eq_true, decide_eq_true_eq, decide_eq_true_eq]
  exact ⟨fun h => h.imp Eq.symm Eq.symm, fun h => h.imp Eq.symm Eq.symm⟩

theorem f15a_fld_lt {L o i : ℕ} (h : (fld(L, o, M128)).testBit i = true) : i < 128 := by
  change (L >>> o &&& (2 ^ 128 - 1)).testBit i = true at h
  rw [Nat.testBit_and, Nat.testBit_two_pow_sub_one, Bool.and_eq_true, decide_eq_true_eq] at h
  exact h.2

theorem f15a_cenE_lt {X y i : ℕ} (h : (cenE P C X y).testBit i = true) : i < 128 := by
  have e : cenE P C X y = Nat.rec (motive := fun _ => Nat) 0 (fun i acc =>
      nIf(bAnd(hasB X i, Nat.beq (atR (rowT P i) y) (atR (rowT C i) y)),
        Nat.lor acc (Nat.shiftLeft 1 i), acc)) 128 := by
    simp only [cenE, strictN_eq]
  rw [e, recMask_bit] at h
  obtain ⟨j, hj, -, rfl⟩ := h
  exact hj

theorem f15a_listAnd_iff (f : ℕ → Bool) : ∀ l : List ℕ,
    List.rec (motive := fun _ => Bool) true (fun c _ ih => f c && ih) l = true ↔
      ∀ c ∈ l, f c = true
  | [] => by simp
  | c :: l => by
    change (f c && List.rec (motive := fun _ => Bool) true (fun c _ ih => f c && ih) l) =
      true ↔ _
    rw [Bool.and_eq_true, f15a_listAnd_iff f l, List.forall_mem_cons]

theorem f15a_subM {X Y : ℕ} (h : subM X Y = true) : mset elt X ⊆ mset elt Y :=
  subset_of_land (Nat.eq_of_beq_eq_true h)

theorem f15a_mset_land (hinj : ∀ i < 128, ∀ j < 128, elt i = elt j → i = j) (A B : ℕ) :
    mset elt (Nat.land A B) = mset elt A ∩ mset elt B := by
  ext g
  simp only [mset, Set.mem_setOf_eq, Set.mem_inter_iff, hasB_eq]
  change (∃ i < 128, (A &&& B).testBit i = true ∧ elt i = g) ↔ _
  simp only [Nat.testBit_and, Bool.and_eq_true]
  constructor
  · rintro ⟨i, hi, ⟨h1, h2⟩, he⟩
    exact ⟨⟨i, hi, h1, he⟩, ⟨i, hi, h2, he⟩⟩
  · rintro ⟨⟨i, hi, h1, rfl⟩, ⟨j, hj, h2, he⟩⟩
    rw [hinj j hj i hi he] at h2
    exact ⟨i, hi, ⟨h1, h2⟩, rfl⟩

section Tables

variable (hR : RealT elt P C V Q)
include hR

theorem f15a_cenS (X : ℕ) (gs : List ℕ) (hgs : ∀ g ∈ gs, g < 128) :
    mset elt (cenS P C X gs) = {x | x ∈ mset elt X ∧ ∀ g ∈ gs, x * elt g = elt g * x} := by
  induction gs with
  | nil =>
    ext x
    simp only [List.not_mem_nil, false_imp_iff, imp_true_iff, and_true, Set.mem_setOf_eq]
    rfl
  | cons g gs ih =>
    change mset elt (cenE P C (cenS P C X gs) g) = _
    rw [cenE_mset hR _ (hgs g (by simp)), ih (fun g' hg' => hgs g' (by simp [hg']))]
    ext x
    simp only [Set.mem_setOf_eq, List.mem_cons, forall_eq_or_imp]
    tauto

theorem f15a_upS (X Zm : ℕ) (gs : List ℕ) (hgs : ∀ g ∈ gs, g < 128) :
    mset elt (upS P C V X Zm gs) =
      {x | x ∈ mset elt X ∧ ∀ g ∈ gs, ⁅x, elt g⁆ ∈ mset elt Zm} := by
  simp only [upS, strictN_eq]
  rw [mset_recMaskId]
  ext x
  simp only [Set.mem_setOf_eq]
  simp only [bAnd_eq, Bool.and_eq_true, f15a_listAnd_iff]
  constructor
  · rintro ⟨i, hi, ⟨hX, hc⟩, rfl⟩
    refine ⟨(mem_mset_iff hR.inj hi).2 hX, fun g hg => ?_⟩
    rw [← commE_elt hR hi (hgs g hg)]
    exact (mem_mset_iff hR.inj (atR_lt _ _)).2 (hc g hg)
  · rintro ⟨⟨i, hi, hX, rfl⟩, hc⟩
    refine ⟨i, hi, ⟨hX, fun g hg => ?_⟩, rfl⟩
    have := hc g hg
    rw [← commE_elt hR hi (hgs g hg)] at this
    exact (mem_mset_iff hR.inj (atR_lt _ _)).1 this

theorem f15a_conjM {s : ℕ} (hs : s < 128) (X : ℕ) :
    mset elt (conjM P C V s X) = {y | ∃ x ∈ mset elt X, elt s * x * (elt s)⁻¹ = y} := by
  simp only [conjM, strictN_eq]
  rw [mset_recMask (fun i => hasB X i) (fun i => conjR (rowT P s) (rowT C (atR V s)) i)
    (fun i _ => atR_lt _ _)]
  ext y
  simp only [Set.mem_setOf_eq]
  constructor
  · rintro ⟨i, hi, hb, rfl⟩
    exact ⟨elt i, ⟨i, hi, hb, rfl⟩, (conjR_elt hR hs hi).symm⟩
  · rintro ⟨_, ⟨i, hi, hb, rfl⟩, rfl⟩
    exact ⟨i, hi, hb, conjR_elt hR hs hi⟩

theorem f15a_normM {X N : ℕ} (h : normM P C V X N = true) :
    ∀ x ∈ mset elt X, ∀ n ∈ mset elt N, x * n * x⁻¹ ∈ mset elt N := by
  simp only [normM, strictB_eq] at h
  rintro _ ⟨i, hi, hb, rfl⟩ n hn
  have := allBelow_spec h (by decide) i hi
  rw [hb] at this
  have e := Nat.eq_of_beq_eq_true this
  rw [← e, f15a_conjM hR hi]
  exact ⟨n, hn, rfl⟩

theorem f15a_sq (X : ℕ) : mset elt (imgR Q X) = (fun x => x * x) '' mset elt X :=
  mset_imgR Q X _ fun _ hi => hR.sq hi

theorem f15a_card (m : ℕ) : (mset elt m).ncard = pop m :=
  pop_sound hR.inj (repM_mset hR.inj m)

end Tables

theorem f15a_comm_closure {N : Subgroup Γ} {s : Set Γ}
    (hn : ∀ t ∈ closure s, ∀ n ∈ N, t * n * t⁻¹ ∈ N) {x : Γ} (hx : ∀ g ∈ s, ⁅x, g⁆ ∈ N) :
    ∀ y ∈ closure s, ⁅x, y⁆ ∈ N := by
  intro y hy
  induction hy using Subgroup.closure_induction with
  | mem g hg => exact hx g hg
  | one => simp [commutatorElement_def]
  | mul a b ha hb iha ihb =>
    have e : ⁅x, a * b⁆ = ⁅x, a⁆ * (a * ⁅x, b⁆ * a⁻¹) := by
      simp only [commutatorElement_def]
      group
    rw [e]
    exact N.mul_mem iha (hn a ha _ ihb)
  | inv a ha iha =>
    have e : ⁅x, a⁻¹⁆ = a⁻¹ * ⁅x, a⁆⁻¹ * a⁻¹⁻¹ := by
      simp only [commutatorElement_def]
      group
    rw [e]
    exact hn _ (inv_mem ha) _ (N.inv_mem iha)

theorem f15a_zSeries_conj (k : ℕ) (T : Subgroup Γ) :
    ∀ t ∈ T, ∀ n ∈ zSeries k T, t * n * t⁻¹ ∈ zSeries k T := by
  rintro t ht _ ⟨w, hw, rfl⟩
  refine ⟨⟨t, ht⟩ * w * ⟨t, ht⟩⁻¹,
    (inferInstance : (Subgroup.upperCentralSeries ↥T k).Normal).conj_mem w hw _, ?_⟩
  simp

theorem f15a_zSeries_zero (T : Subgroup Γ) : zSeries 0 T = ⊥ := by
  rw [zSeries, Subgroup.upperCentralSeries_zero, Subgroup.map_bot]

theorem f15a_zSeries_succ (k : ℕ) {s : Set Γ} :
    (zSeries (k + 1) (closure s) : Set Γ) =
      {x | x ∈ closure s ∧ ∀ g ∈ s, ⁅x, g⁆ ∈ zSeries k (closure s)} := by
  ext x
  simp only [SetLike.mem_coe, Set.mem_setOf_eq,
    CFSG.OddStandard.HigherRank.G2Three.Sec1Proof.Tab.mem_zSeries_succ]
  refine and_congr_right fun _ => ⟨fun h g hg => h g (subset_closure hg), fun h => ?_⟩
  exact f15a_comm_closure (f15a_zSeries_conj k _) h

theorem f15a_cen_eq {s : Set Γ} :
    (cen (closure s) : Set Γ) = {x | x ∈ closure s ∧ ∀ g ∈ s, x * g = g * x} := by
  ext x
  simp only [cen, coe_inf, Set.mem_inter_iff, SetLike.mem_coe, mem_centralizer_iff,
    Set.mem_setOf_eq]
  refine and_congr_right fun _ => ⟨fun h g hg => (h g (subset_closure hg)).symm, fun h y hy => ?_⟩
  have := f15a_comm_closure (N := ⊥) (fun t _ n hn => by
    rw [mem_bot] at hn ⊢; rw [hn]; group) (x := x) (fun g hg => by
      rw [mem_bot, commutatorElement_eq_one_iff_mul_comm]; exact h g hg) y hy
  rw [mem_bot, commutatorElement_eq_one_iff_mul_comm] at this
  exact this.symm

theorem f15a_zSeries_one {s : Set Γ} : zSeries 1 (closure s) = cen (closure s) := by
  apply SetLike.coe_injective
  rw [f15a_zSeries_succ 0, f15a_zSeries_zero, f15a_cen_eq]
  ext x
  simp only [Set.mem_setOf_eq, mem_bot, commutatorElement_eq_one_iff_mul_comm]

theorem f15a_normal {T N : Subgroup Γ} (hn : ∀ t ∈ T, ∀ n ∈ N, t * n * t⁻¹ ∈ N) :
    (N.subgroupOf T).Normal :=
  ⟨fun n hmem g => by
    rw [mem_subgroupOf] at hmem ⊢
    simpa using hn g.1 g.2 n hmem⟩

theorem f15a_mk_sq {T N : Subgroup Γ} [(N.subgroupOf T).Normal] (t : ↥T) :
    (QuotientGroup.mk' (N.subgroupOf T) t) * QuotientGroup.mk' (N.subgroupOf T) t = 1 ↔
      (t : Γ) * t ∈ N := by
  rw [← map_mul, QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff, mem_subgroupOf]
  rfl

theorem f15a_card_sub {T : Subgroup Γ} : Nat.card T = (T : Set Γ).ncard := by
  rw [← Nat.card_coe_set_eq]
  rfl

theorem f15a_secE [Finite Γ] {T N : Subgroup Γ} {k : ℕ} (hNT : N ≤ T)
    (hn : ∀ t ∈ T, ∀ n ∈ N, t * n * t⁻¹ ∈ N) (hsq : ∀ t ∈ T, t * t ∈ N)
    (hc : (T : Set Γ).ncard = 2 ^ k * (N : Set Γ).ncard) :
    SecProp T N (fun Y _ _ _ => IsE k Y) := by
  haveI hnorm := f15a_normal hn
  refine ⟨hnorm, ?_, ?_⟩
  · have hq : ∀ q : ↥T ⧸ N.subgroupOf T, q * q = 1 := by
      intro q
      induction q using QuotientGroup.induction_on with
      | H t => exact (f15a_mk_sq t).2 (hsq t.1 t.2)
    exact isElemAbelian_iff_sq.2 fun y _ => hq y
  · have h1 := Subgroup.card_eq_card_quotient_mul_card_subgroup (N.subgroupOf T)
    have h2 : Nat.card (N.subgroupOf T) = Nat.card N :=
      Nat.card_congr (Subgroup.subgroupOfEquivOfLe hNT).toEquiv
    rw [h2, f15a_card_sub, hc, ← f15a_card_sub] at h1
    have hpos : 0 < Nat.card N := Nat.card_pos
    exact (Nat.eq_of_mul_eq_mul_right hpos h1).symm

def f15aP (T N K : Subgroup Γ) : Prop := N ≤ K ∧ K ≤ T ∧ ∀ x ∈ K, x * x ∈ N

theorem f15a_secMax [Finite Γ] {T N X₁ X₂ : Subgroup Γ} (hNT : N ≤ T)
    (hn : ∀ t ∈ T, ∀ n ∈ N, t * n * t⁻¹ ∈ N)
    (hmax : ∀ K : Subgroup Γ,
      (f15aP T N K ∧ ∀ K', f15aP T N K' → K ≤ K' → K = K') ↔ K = X₁ ∨ K = X₂) :
    SecProp T N (fun Y _ _ π => maxElemAbelian (⊤ : Subgroup Y) =
      {(X₁.subgroupOf T).map π, (X₂.subgroupOf T).map π}) := by
  haveI hnorm := f15a_normal hn
  refine ⟨hnorm, ?_⟩
  set π := QuotientGroup.mk' (N.subgroupOf T)
  have hsurj : Function.Surjective π := QuotientGroup.mk'_surjective _
  let pre : Subgroup (↥T ⧸ N.subgroupOf T) → Subgroup Γ := fun Y => (Y.comap π).map T.subtype
  have mem_pre : ∀ Y x, x ∈ pre Y ↔ ∃ h : x ∈ T, π ⟨x, h⟩ ∈ Y := by
    intro Y x
    simp only [pre, mem_map, mem_comap, Subgroup.coe_subtype]
    constructor
    · rintro ⟨t, ht, rfl⟩
      exact ⟨t.2, ht⟩
    · rintro ⟨h, hx⟩
      exact ⟨⟨x, h⟩, hx, rfl⟩
  have pre_le : ∀ Y, pre Y ≤ T := fun Y x hx => ((mem_pre Y x).1 hx).1
  have pre_ge : ∀ Y, N ≤ pre Y := by
    intro Y x hx
    refine (mem_pre Y x).2 ⟨hNT hx, ?_⟩
    have : π ⟨x, hNT hx⟩ = 1 := by
      rw [QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff, mem_subgroupOf]
      exact hx
    rw [this]
    exact Y.one_mem
  have map_pre : ∀ Y, ((pre Y).subgroupOf T).map π = Y := by
    intro Y
    change (((Y.comap π).map T.subtype).subgroupOf T).map π = Y
    have e : ((Y.comap π).map T.subtype).subgroupOf T = Y.comap π :=
      Subgroup.comap_map_eq_self_of_injective T.subtype_injective _
    rw [e]
    exact Subgroup.map_comap_eq_self_of_surjective hsurj Y
  have pre_map : ∀ K : Subgroup Γ, N ≤ K → K ≤ T → pre ((K.subgroupOf T).map π) = K := by
    intro K hNK hKT
    ext x
    rw [mem_pre]
    constructor
    · rintro ⟨h, hx⟩
      obtain ⟨k, hk, he⟩ := mem_map.1 hx
      rw [mem_subgroupOf] at hk
      have e := QuotientGroup.eq.1 he
      rw [mem_subgroupOf] at e
      have : (x : Γ) = k * ((k : Γ)⁻¹ * x) := by group
      rw [this]
      refine K.mul_mem hk (hNK ?_)
      simpa using e
    · intro hx
      exact ⟨hKT hx, mem_map.2 ⟨⟨x, hKT hx⟩, by rw [mem_subgroupOf]; exact hx, rfl⟩⟩
  have ea_iff : ∀ Y, IsElemAbelian 2 Y ↔ ∀ x ∈ pre Y, x * x ∈ N := by
    intro Y
    constructor
    · intro h x hx
      obtain ⟨hxT, hy⟩ := (mem_pre Y x).1 hx
      exact (f15a_mk_sq ⟨x, hxT⟩).1 (isElemAbelian_iff_sq.1 h _ hy)
    · intro h
      refine isElemAbelian_iff_sq.2 fun y hy => ?_
      obtain ⟨t, rfl⟩ := hsurj y
      exact (f15a_mk_sq t).2 (h t ((mem_pre Y t).2 ⟨t.2, hy⟩))
  have P_pre : ∀ Y, IsElemAbelian 2 Y → f15aP T N (pre Y) :=
    fun Y h => ⟨pre_ge Y, pre_le Y, (ea_iff Y).1 h⟩
  have ea_map : ∀ K, f15aP T N K → IsElemAbelian 2 ((K.subgroupOf T).map π) := by
    intro K hK
    rw [ea_iff, pre_map K hK.1 hK.2.1]
    exact hK.2.2
  ext Y
  simp only [maxElemAbelian, Set.mem_setOf_eq, Set.mem_insert_iff, Set.mem_singleton_iff]
  constructor
  · rintro ⟨-, hEA, hY⟩
    have hK : f15aP T N (pre Y) ∧ ∀ K', f15aP T N K' → pre Y ≤ K' → pre Y = K' := by
      refine ⟨P_pre Y hEA, fun K' hK' hle => ?_⟩
      have hYle : Y ≤ (K'.subgroupOf T).map π := by
        rw [← map_pre Y]
        exact map_mono (fun x hx => by rw [mem_subgroupOf] at hx ⊢; exact hle hx)
      have := hY _ hYle le_top (ea_map K' hK')
      rw [← pre_map K' hK'.1 hK'.2.1, this]
    rcases (hmax _).1 hK with h | h
    · left
      rw [← map_pre Y, h]
    · right
      rw [← map_pre Y, h]
  · intro hY
    have hX : ∀ X, (X = X₁ ∨ X = X₂) → Y = (X.subgroupOf T).map π →
        Y ≤ ⊤ ∧ IsElemAbelian 2 Y ∧
          ∀ Y', Y ≤ Y' → Y' ≤ ⊤ → IsElemAbelian 2 Y' → Y' = Y := by
      intro X hX hYX
      obtain ⟨hP, hm⟩ := (hmax X).2 hX
      refine ⟨le_top, hYX ▸ ea_map X hP, fun Y' hle _ hEA => ?_⟩
      have hpre : X ≤ pre Y' := by
        rw [← pre_map X hP.1 hP.2.1, ← hYX]
        intro x hx
        obtain ⟨h, hx⟩ := (mem_pre Y x).1 hx
        exact (mem_pre Y' x).2 ⟨h, hle hx⟩
      have := hm _ (P_pre Y' hEA) hpre
      rw [← map_pre Y', ← this, hYX]
    rcases hY with h | h
    · exact hX X₁ (Or.inl rfl) h
    · exact hX X₂ (Or.inr rfl) h

@[expose] def f15a_q8Code : QuaternionGroup 2 → ℕ
  | .a i => i.val
  | .xa i => 4 + i.val

theorem f15a_q8Code_lt : ∀ a, f15a_q8Code a < 8 := by decide

theorem f15a_q8Code_surj : ∀ t : Fin 8, ∃ a, f15a_q8Code a = t.val := by decide

theorem f15a_q8M_code : ∀ a b : QuaternionGroup 2,
    q8M (f15a_q8Code a) (f15a_q8Code b) = f15a_q8Code (a * b) := by decide

theorem f15a_pair {u v : ℕ} (hu : u < 8) (hv : v < 8) :
    Nat.shiftRight (8 * u + v) 3 = u ∧ Nat.land (8 * u + v) 7 = v := by
  constructor
  · change (8 * u + v) >>> 3 = u
    rw [Nat.shiftRight_eq_div_pow]
    omega
  · change (8 * u + v) &&& (2 ^ 3 - 1) = v
    rw [Nat.and_two_pow_sub_one_eq_mod]
    omega

theorem f15a_card_pre [Finite Γ] {T N : Subgroup Γ} [(N.subgroupOf T).Normal] (hNT : N ≤ T)
    (W : Set (↥T ⧸ N.subgroupOf T)) :
    (Subtype.val '' (QuotientGroup.mk' (N.subgroupOf T) ⁻¹' W) : Set Γ).ncard =
      Nat.card N * W.ncard := by
  rw [Set.ncard_image_of_injective _ Subtype.val_injective, ← Nat.card_coe_set_eq,
    QuotientGroup.coe_mk', QuotientGroup.card_preimage_mk, Nat.card_coe_set_eq]
  rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe hNT).toEquiv]

section Tables

variable (hR : RealT elt P C V Q)
include hR

theorem f15a_q8U (r s N : ℕ) :
    mset elt (q8U P r s N) = {x | ∃ k < 8, ∃ n ∈ mset elt N, elt (d8I P r s k) * n = x} := by
  have e : q8U P r s N = Nat.rec (motive := fun _ => Nat) 0
      (fun k acc => Nat.lor acc (imgR (rowT P (d8I P r s k)) N)) 8 := by
    simp only [q8U, strictN_eq]
  rw [e]
  ext x
  constructor
  · rintro ⟨i, hi, hb, rfl⟩
    rw [hasB_eq, recLor_bit] at hb
    obtain ⟨t, ht, hb⟩ := hb
    have hm : elt i ∈ mset elt (imgR (rowT P (d8I P r s t)) N) :=
      ⟨i, hi, by rw [hasB_eq]; exact hb, rfl⟩
    rw [mset_imgR_left hR (d8I_lt _ _ _)] at hm
    obtain ⟨n, hn, he⟩ := hm
    exact ⟨t, ht, n, hn, he⟩
  · rintro ⟨t, ht, n, hn, rfl⟩
    have hm : elt (d8I P r s t) * n ∈ mset elt (imgR (rowT P (d8I P r s t)) N) := by
      rw [mset_imgR_left hR (d8I_lt _ _ _)]
      exact ⟨n, hn, rfl⟩
    obtain ⟨i, hi, hb, he⟩ := hm
    refine ⟨i, hi, ?_, he⟩
    rw [hasB_eq] at hb ⊢
    exact (recLor_bit (fun k => imgR (rowT P (d8I P r s k)) N) i 8).2 ⟨t, ht, hb⟩

theorem f15a_q8mod {r s N : ℕ} (h : q8modK P V r s N = true) :
    ∀ u < 8, ∀ v < 8, (elt (d8I P r s (q8M u v)))⁻¹ * (elt (d8I P r s u) * elt (d8I P r s v)) ∈
      mset elt N := by
  intro u hu v hv
  simp only [q8modK, strictB_eq] at h
  have := allBelow_spec h (by decide) (8 * u + v) (by omega)
  obtain ⟨e1, e2⟩ := f15a_pair hu hv
  rw [e1, e2] at this
  have hm := (mem_mset_iff hR.inj (atR_lt _ _)).2 this
  change elt (mulE P (atR V (d8I P r s (q8M u v))) (mulE P (d8I P r s u) (d8I P r s v))) ∈
    mset elt N at hm
  rwa [mulE_elt hR (x := atR V (d8I P r s (q8M u v))) (y := mulE P (d8I P r s u) (d8I P r s v))
    (atR_lt _ _) (atR_lt _ _), hR.inv (d8I_lt _ _ _),
    mulE_elt hR (d8I_lt _ _ _) (d8I_lt _ _ _)] at hm

theorem f15a_q8map [Finite Γ] {X Nm r s : ℕ} {T N : Subgroup Γ} [(N.subgroupOf T).Normal]
    (hX : mset elt X = T) (hN : mset elt Nm = N) (hNT : N ≤ T)
    (hm : q8modK P V r s Nm = true) (hc : pop (q8U P r s Nm) = 8 * pop Nm)
    (hs : subM (q8U P r s Nm) X = true) :
    ∃ φ : QuaternionGroup 2 →* ↥T ⧸ N.subgroupOf T, Function.Injective φ ∧
      (∀ c, ∃ h : elt (d8I P r s (f15a_q8Code c)) ∈ T,
        φ c = QuotientGroup.mk' (N.subgroupOf T) ⟨_, h⟩) ∧
      mset elt (q8U P r s Nm) = Subtype.val '' (QuotientGroup.mk' (N.subgroupOf T) ⁻¹' Set.range φ) := by
  classical
  set π := QuotientGroup.mk' (N.subgroupOf T)
  have hU := f15a_q8U hR r s Nm
  have hmemU : ∀ k < 8, elt (d8I P r s k) ∈ mset elt (q8U P r s Nm) := fun k hk => by
    rw [hU]
    refine ⟨k, hk, 1, ?_, mul_one _⟩
    rw [hN]
    exact N.one_mem
  have hmem : ∀ c, elt (d8I P r s (f15a_q8Code c)) ∈ T := fun c => by
    have := f15a_subM hs (hmemU _ (f15a_q8Code_lt c))
    rwa [hX] at this
  have hspec := f15a_q8mod hR hm
  let φ : QuaternionGroup 2 →* ↥T ⧸ N.subgroupOf T :=
    { toFun := fun c => π ⟨_, hmem c⟩
      map_one' := by
        have e : (⟨_, hmem 1⟩ : ↥T) = 1 := by
          apply Subtype.ext
          change elt (d8I P r s 0) = 1
          exact hR.one
        change π ⟨_, hmem 1⟩ = 1
        rw [e, map_one]
      map_mul' := fun a b => by
        change π ⟨_, hmem (a * b)⟩ = π ⟨_, hmem a⟩ * π ⟨_, hmem b⟩
        rw [← map_mul, QuotientGroup.mk'_apply, QuotientGroup.mk'_apply, QuotientGroup.eq,
          mem_subgroupOf, ← SetLike.mem_coe, ← hN]
        have := hspec _ (f15a_q8Code_lt a) _ (f15a_q8Code_lt b)
        rw [f15a_q8M_code] at this
        simpa using this }
  have hpre : mset elt (q8U P r s Nm) = Subtype.val '' (π ⁻¹' Set.range φ) := by
    ext x
    constructor
    · intro hx
      have hxT : x ∈ T := by
        have := f15a_subM hs hx
        rwa [hX] at this
      rw [hU] at hx
      obtain ⟨k, hk, n, hn, rfl⟩ := hx
      obtain ⟨c, hc⟩ := f15a_q8Code_surj ⟨k, hk⟩
      refine ⟨⟨_, hxT⟩, ⟨c, ?_⟩, rfl⟩
      change π ⟨_, hmem c⟩ = π ⟨_, hxT⟩
      rw [QuotientGroup.mk'_apply, QuotientGroup.mk'_apply, QuotientGroup.eq, mem_subgroupOf,
        ← SetLike.mem_coe, ← hN]
      simp only [Subgroup.coe_mul, Subgroup.coe_inv]
      change (elt (d8I P r s (f15a_q8Code c)))⁻¹ * (elt (d8I P r s k) * n) ∈ _
      rw [hc]
      simpa using hn
    · rintro ⟨t, ⟨c, hct⟩, rfl⟩
      change π ⟨_, hmem c⟩ = π t at hct
      rw [QuotientGroup.mk'_apply, QuotientGroup.mk'_apply, QuotientGroup.eq, mem_subgroupOf,
        ← SetLike.mem_coe, ← hN] at hct
      rw [hU]
      refine ⟨_, f15a_q8Code_lt c, _, hct, ?_⟩
      simp
  refine ⟨φ, ?_, fun c => ⟨hmem c, rfl⟩, hpre⟩
  have hcard : (Set.range φ).ncard = 8 := by
    have h1 := f15a_card_pre hNT (Set.range φ)
    rw [← hpre, f15a_card hR, hc, ← f15a_card hR, hN, ← f15a_card_sub] at h1
    have hpos : 0 < Nat.card N := Nat.card_pos
    rw [mul_comm] at h1
    exact (Nat.eq_of_mul_eq_mul_left hpos h1).symm
  have hfin : (Finset.univ.image φ).card = (Finset.univ : Finset (QuaternionGroup 2)).card := by
    rw [Finset.card_univ, QuaternionGroup.card, ← Set.ncard_coe_finset, Finset.coe_image,
      Finset.coe_univ, Set.image_univ, hcard]
  intro a b hab
  exact (Finset.card_image_iff.1 hfin) (Finset.mem_coe.2 (Finset.mem_univ a))
    (Finset.mem_coe.2 (Finset.mem_univ b)) hab

theorem f15a_q8q8 [Finite Γ] {X Nm r1 s1 r2 s2 : ℕ} {T N : Subgroup Γ}
    (hX : mset elt X = T) (hN : mset elt Nm = N)
    (h : q8q8modK P C V X Nm r1 s1 r2 s2 = true) :
    SecProp T N (fun Y _ _ _ => IsQ8StarQ8 Y) := by
  simp only [q8q8modK, strictB_eq, bAnd_eq, Bool.and_eq_true, Nat.beq_eq] at h
  obtain ⟨hsub, hnorm, hm1, hm2, hc1, hc2, hs1, hs2, hcomm, hprod, hcap⟩ := h
  have hNT : N ≤ T := by
    intro x hx
    have := f15a_subM (elt := elt) hsub
    rw [hX, hN] at this
    exact this hx
  have hn : ∀ t ∈ T, ∀ n ∈ N, t * n * t⁻¹ ∈ N := by
    intro t ht n hn
    have := f15a_normM hR hnorm
    rw [hX, hN] at this
    exact this t ht n hn
  have hnor := f15a_normal hn
  refine ⟨hnor, ?_⟩
  set π := QuotientGroup.mk' (N.subgroupOf T)
  obtain ⟨φ₁, hi₁, he₁, hp₁⟩ := f15a_q8map hR hX hN hNT hm1 hc1 hs1
  obtain ⟨φ₂, hi₂, he₂, hp₂⟩ := f15a_q8map hR hX hN hNT hm2 hc2 hs2
  refine ⟨φ₁.range, φ₂.range, ⟨(MonoidHom.ofInjective hi₁).symm⟩,
    ⟨(MonoidHom.ofInjective hi₂).symm⟩, ?_, ?_, ?_⟩
  · rintro _ ⟨a, rfl⟩ _ ⟨b, rfl⟩
    obtain ⟨ha, ea⟩ := he₁ a
    obtain ⟨hb, eb⟩ := he₂ b
    rw [ea, eb, ← commutatorElement_eq_one_iff_mul_comm, ← map_commutatorElement,
      QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff, mem_subgroupOf, ← SetLike.mem_coe, ← hN]
    have := allBelow_spec hcomm (by decide) (8 * f15a_q8Code a + f15a_q8Code b)
      (by have := f15a_q8Code_lt a; have := f15a_q8Code_lt b; omega)
    obtain ⟨e1, e2⟩ := f15a_pair (f15a_q8Code_lt a) (f15a_q8Code_lt b)
    rw [e1, e2] at this
    have hm := (mem_mset_iff hR.inj (atR_lt _ _)).2 this
    change elt (commE P C V (d8I P r1 s1 (f15a_q8Code a)) (d8I P r2 s2 (f15a_q8Code b))) ∈
      mset elt Nm at hm
    rw [commE_elt hR (d8I_lt _ _ _) (d8I_lt _ _ _)] at hm
    simpa [commutatorElement_def] using hm
  · rw [eq_top_iff]
    intro q _
    obtain ⟨t, rfl⟩ := QuotientGroup.mk'_surjective (N.subgroupOf T) q
    have ht : (t : Γ) ∈ mset elt X := by rw [hX]; exact t.2
    rw [← hprod, prodM_mset hR, hp₁, hp₂] at ht
    obtain ⟨_, ⟨a, ha, rfl⟩, _, ⟨b, hb, rfl⟩, hab⟩ := ht
    have : t = a * b := Subtype.ext hab.symm
    rw [this, map_mul]
    exact mul_mem (mem_sup_left ha) (mem_sup_right hb)
  · have h1 := f15a_card_pre hNT (Set.range φ₁ ∩ Set.range φ₂)
    rw [Set.preimage_inter, Set.image_inter Subtype.val_injective, ← hp₁, ← hp₂,
      ← f15a_mset_land hR.inj, f15a_card hR, hcap, ← f15a_card hR, hN, ← f15a_card_sub] at h1
    have hpos : 0 < Nat.card N := Nat.card_pos
    rw [f15a_card_sub, coe_inf, MonoidHom.coe_range, MonoidHom.coe_range]
    rw [mul_comm] at h1
    exact (Nat.eq_of_mul_eq_mul_right hpos h1).symm

theorem f15a_secEK [Finite Γ] {X Nm f k : ℕ} {T N : Subgroup Γ} (hf : f = 2 ^ k)
    (hX : mset elt X = T) (hN : mset elt Nm = N) (h : secEK P C V Q X Nm f = true) :
    SecProp T N (fun Y _ _ _ => IsE k Y) := by
  simp only [secEK, bAnd_eq, Bool.and_eq_true, Nat.beq_eq] at h
  obtain ⟨hsub, hnorm, hsq, hc⟩ := h
  have hNT : N ≤ T := by
    intro x hx
    have := f15a_subM (elt := elt) hsub
    rw [hX, hN] at this
    exact this hx
  refine f15a_secE hNT ?_ ?_ ?_
  · intro t ht n hn
    have := f15a_normM hR hnorm
    rw [hX, hN] at this
    exact this t ht n hn
  · intro t ht
    have := f15a_subM (elt := elt) hsq
    rw [f15a_sq hR, hX, hN] at this
    exact this ⟨t, ht, rfl⟩
  · rw [← hX, ← hN, f15a_card hR, f15a_card hR, hc, hf]
    rfl

theorem f15a_cenS_cen {X : ℕ} {gs : List ℕ} (hgs : ∀ g ∈ gs, g < 128) {T : Subgroup Γ}
    (hT : mset elt X = T) (hTc : T = closure {x | ∃ g ∈ gs, elt g = x}) :
    mset elt (cenS P C X gs) = cen T := by
  subst hTc
  rw [f15a_cenS hR X gs hgs, hT, f15a_cen_eq]
  ext x
  simp only [Set.mem_setOf_eq, SetLike.mem_coe]
  exact and_congr_right fun _ =>
    ⟨fun h _ ⟨g, hg, he⟩ => he ▸ h g hg, fun h g hg => h _ ⟨g, hg, rfl⟩⟩

theorem f15a_upS_z {X Zm : ℕ} {gs : List ℕ} (hgs : ∀ g ∈ gs, g < 128) {T : Subgroup Γ}
    (hT : mset elt X = T) (hTc : T = closure {x | ∃ g ∈ gs, elt g = x}) {k : ℕ}
    (hZ : mset elt Zm = zSeries k T) : mset elt (upS P C V X Zm gs) = zSeries (k + 1) T := by
  subst hTc
  rw [f15a_upS hR X Zm gs hgs, hT, hZ, f15a_zSeries_succ]
  ext x
  simp only [Set.mem_setOf_eq, SetLike.mem_coe]
  exact and_congr_right fun _ =>
    ⟨fun h _ ⟨g, hg, he⟩ => he ▸ h g hg, fun h g hg => h _ ⟨g, hg, rfl⟩⟩

theorem f15a_hmax {L m X Nm k1 k2 : ℕ} {T Nz X₁ X₂ : Subgroup Γ} (hm : m ≤ 448)
    (hlat : (∀ k < m, ∃ K : Subgroup Γ, K ≤ T ∧ RepM elt (latM L k) (K : Set Γ)) ∧
      ∀ K ≤ T, ∃ k < m, RepM elt (latM L k) (K : Set Γ))
    (hX : mset elt X = T) (hN : mset elt Nm = Nz) (hNb : ∀ i, Nm.testBit i = true → i < 128)
    (h : eaMaxK Q L m X Nm k1 k2 = true) (h1 : mset elt (entL L k1) = X₁)
    (h2 : mset elt (entL L k2) = X₂) :
    ∀ K : Subgroup Γ, (f15aP T Nz K ∧ ∀ K', f15aP T Nz K' → K ≤ K' → K = K') ↔
      K = X₁ ∨ K = X₂ := by
  simp only [eaMaxK, bAnd_eq, Bool.and_eq_true, Nat.beq_eq] at h
  obtain ⟨-, hmx⟩ := h
  have hmx' : ∀ k, hasB (maxIdx L (secC Q L m X Nm) m) k = true ↔ k = k1 ∨ k = k2 :=
    fun k => by rw [hmx, hasB_eq, f15a_two_bit]
  have hent : ∀ k i, (entL L k).testBit i = true → i < 128 := fun k i hi => f15a_fld_lt hi
  have hsubI : ∀ {a b : ℕ}, (∀ i, a.testBit i = true → i < 128) →
      (subM a b = true ↔ mset elt a ⊆ mset elt b) :=
    fun ha => subM_iff_subset hR.inj (lt128_of_testBit ha)
  have hC : ∀ k (K : Subgroup Γ), mset elt (entL L k) = K →
      (hasB (secC Q L m X Nm) k = true ↔ k < m ∧ f15aP T Nz K) := by
    intro k K hK
    rw [secC_bit hm, hsubI hNb,
      hsubI (hent k), hsubI (fun i hi => testBit_imgR_lt hi), f15a_sq hR, hK, hN, hX]
    simp only [f15aP, Set.image_subset_iff, SetLike.coe_subset_coe]
    rfl
  intro K
  constructor
  · rintro ⟨hP, hmaxK⟩
    obtain ⟨k, hk, hrep⟩ := hlat.2 K hP.2.1
    have hK : mset elt (entL L k) = K := hrep.eq_mset.symm
    have hin : hasB (maxIdx L (secC Q L m X Nm) m) k = true := by
      rw [maxIdx_bit hm]
      refine ⟨hk, (hC k K hK).2 ⟨hk, hP⟩, fun k' hk' hc' hs => ?_⟩
      obtain ⟨K', -, hrep'⟩ := hlat.1 k' hk'
      have hK' : mset elt (entL L k') = K' := hrep'.eq_mset.symm
      have hP' := ((hC k' K' hK').1 hc').2
      have hle : K ≤ K' := by
        rw [← SetLike.coe_subset_coe, ← hK, ← hK']
        exact f15a_subM hs
      have := hmaxK K' hP' hle
      apply eq_of_mset_eq hR.inj (hent k) (hent k')
      rw [hK, hK', this]
    rcases (hmx' k).1 hin with rfl | rfl
    · left
      apply SetLike.coe_injective
      rw [← hK, h1]
    · right
      apply SetLike.coe_injective
      rw [← hK, h2]
  · intro hK
    have key : ∀ k, mset elt (entL L k) = K → hasB (maxIdx L (secC Q L m X Nm) m) k = true →
        f15aP T Nz K ∧ ∀ K', f15aP T Nz K' → K ≤ K' → K = K' := by
      intro k hK hin
      rw [maxIdx_bit hm] at hin
      obtain ⟨-, hc, hmaxk⟩ := hin
      refine ⟨((hC k K hK).1 hc).2, fun K' hP' hle => ?_⟩
      obtain ⟨k', hk', hrep'⟩ := hlat.2 K' hP'.2.1
      have hK' : mset elt (entL L k') = K' := hrep'.eq_mset.symm
      have hc' := (hC k' K' hK').2 ⟨hk', hP'⟩
      have hs : subM (entL L k) (entL L k') = true := by
        rw [hsubI (hent k), hK, hK']
        exact hle
      have := hmaxk k' hk' hc' hs
      apply SetLike.coe_injective
      rw [← hK, ← hK', this]
    rcases hK with rfl | rfl
    · exact key k1 h1 ((hmx' k1).2 (Or.inl rfl))
    · exact key k2 h2 ((hmx' k2).2 (Or.inr rfl))

end Tables

theorem f15a_centIn (T : Subgroup Γ) (y : Γ) : centIn T (closure {y}) = centEl T y := by
  have e : centralizer ((closure {y} : Subgroup Γ) : Set Γ) = centralizer {y} := by
    ext x
    simp only [mem_centralizer_iff]
    refine ⟨fun h g hg => h g (subset_closure hg), fun h g hg => ?_⟩
    induction hg using Subgroup.closure_induction with
    | mem g hg => exact h g hg
    | one => simp
    | mul a b _ _ ha hb => rw [mul_assoc, hb, ← mul_assoc, ha, mul_assoc]
    | inv a _ ha => rw [inv_mul_eq_iff_eq_mul, ← mul_assoc, ha, mul_inv_cancel_right]
  rw [centIn, centEl, e]

theorem f15a_setOf_four (u v w s : Γ) : {x | x ∈ [u, v, w, s]} = ({u, v, w, s} : Set Γ) := by
  ext x
  simp

theorem fact15_12_of_twin [Finite Γ] {fr : Frame Γ} {elt : ℕ → Γ}
    {P C V Q L N kA kBs r1 s1 r2 s2 R : ℕ} (hR : RealT elt P C V Q)
    (hg : ∀ s < 6, elt (s + 1) = sGen fr s) (hN : N ≤ 448)
    (hlat : (∀ k < N, ∃ K : Subgroup Γ, K ≤ fr.Sσ ∧ RepM elt (latM L k) (K : Set Γ)) ∧
      ∀ K ≤ fr.Sσ, ∃ k < N, RepM elt (latM L k) (K : Set Γ))
    (h : f15aK P C V Q L N 1 2 3 4 5 6 kA kBs r1 s1 r2 s2 R = true) :
    (cen fr.Sσ = fr.Z ∧ zSeries 2 fr.Sσ = cen fr.B ∧ zSeries 3 fr.Sσ = fr.E ⊔ fr.F ∧
      SecProp fr.Sσ (fr.E ⊔ fr.F) (fun Y _ _ _ => IsE 3 Y)) ∧
    (SecProp fr.Sσ (cen fr.B) (fun Y _ _ π =>
        maxElemAbelian (⊤ : Subgroup Y) = {(fr.A.subgroupOf fr.Sσ).map π,
          ((fr.B ⊔ closure {fr.σ}).subgroupOf fr.Sσ).map π}) ∧
      SecProp (fr.B ⊔ closure {fr.σ}) fr.Z (fun Y _ _ _ => IsQ8StarQ8 Y)) := by
  obtain ⟨e1, e2, e3, e4, e5, e6⟩ := f13_gens hg
  obtain ⟨hz, h13, h24, -, h123, -, -⟩ := f13_prods hR hg
  simp only [f15aK, bAnd_eq, strictB_eq, Bool.and_eq_true, Nat.beq_eq] at h
  obtain ⟨c1, c2, c3, c4, c5, c6, c7, c8, c9, hBm, hZ, hZ2, hZ3, hE, hnB, hea, hkA, hkBs, hpr,
    hperm, hq⟩ := h
  have hcl : ∀ gs : List ℕ, (∀ g ∈ gs, g < 128) → closOK C gs R = true →
      mset elt (closK C gs R) = (closure {x | x ∈ gs.map elt} : Set Γ) :=
    fun gs hgs hc => by rw [closK_closure hR hgs hc, f13_setOf_eq_map]
  have hl6 : ∀ g ∈ [1, 2, 3, 4, 5, 6], g < 128 := by simp
  have hlB : ∀ g ∈ [mulE P 1 3, 2, 4, 5], g < 128 := by simp [f13_mulE_lt]
  have hS : mset elt (closK C [1, 2, 3, 4, 5] R) = (fr.S : Set Γ) := by
    rw [hcl _ (by simp) c1]
    simp only [List.map_cons, List.map_nil, e1, e2, e3, e4, e5, f13_setOf_five]
    rfl
  have hSs : mset elt (closK C [1, 2, 3, 4, 5, 6] R) = (fr.Sσ : Set Γ) := by
    rw [hcl _ hl6 c2]
    simp only [List.map_cons, List.map_nil, e1, e2, e3, e4, e5, e6, f13_setOf_six]
    rfl
  have hSsc : fr.Sσ = closure {x | ∃ g ∈ [1, 2, 3, 4, 5, 6], elt g = x} :=
    SetLike.coe_injective (hSs.symm.trans (closK_closure hR hl6 c2))
  have hZm : mset elt (closK C [atR Q 2] R) = (fr.Z : Set Γ) := by
    rw [hcl _ (by simp [atR_lt]) c4]
    simp only [List.map_cons, List.map_nil, hz, f13_setOf_one]
    rw [SFrame.Z, Subgroup.zpowers_eq_closure]
  have hAm : mset elt (closK C [1, 2, 3, 4] R) = (fr.A : Set Γ) := by
    rw [hcl _ (by simp) c5]
    simp only [List.map_cons, List.map_nil, e1, e2, e3, e4, f15a_setOf_four]
    rfl
  have hEm : mset elt (closK C [mulE P 2 4, mulE P (mulE P 1 2) 3, atR Q 2] R) =
      (fr.E : Set Γ) := by
    rw [hcl _ (by simp [f13_mulE_lt, atR_lt]) c6]
    simp only [List.map_cons, List.map_nil, h24, h123, hz, f13_setOf_three]
    rfl
  have hFm : mset elt (closK C [mulE P 1 3, mulE P 2 4, atR Q 2] R) = (fr.F : Set Γ) := by
    rw [hcl _ (by simp [f13_mulE_lt, atR_lt]) c7]
    simp only [List.map_cons, List.map_nil, h13, h24, hz, f13_setOf_three]
    rfl
  have hSg : mset elt (closK C [6] R) = (closure {fr.σ} : Set Γ) := by
    rw [hcl _ (by simp) c8]
    simp only [List.map_cons, List.map_nil, e6, f13_setOf_one]
  have hB : mset elt (cenE P C (closK C [1, 2, 3, 4, 5] R) (mulE P 2 4)) = (fr.B : Set Γ) := by
    rw [f13_cenE hR hS (f13_mulE_lt _ _ _), h24, ← f15a_centIn]
    rfl
  have hB' : mset elt (closK C [mulE P 1 3, 2, 4, 5] R) = (fr.B : Set Γ) := hBm ▸ hB
  have hBc : fr.B = closure {x | ∃ g ∈ [mulE P 1 3, 2, 4, 5], elt g = x} :=
    SetLike.coe_injective (hB'.symm.trans (closK_closure hR hlB c3))
  have hZB := f15a_cenS_cen hR hlB hB hBc
  have h1a : cen fr.Sσ = fr.Z :=
    SetLike.coe_injective (by rw [← f15a_cenS_cen hR hl6 hSs hSsc, hZ, hZm])
  have hz1 : mset elt (closK C [atR Q 2] R) = (zSeries 1 fr.Sσ : Set Γ) := by
    rw [hSsc, f15a_zSeries_one, ← hSsc, h1a, hZm]
  have h1b : zSeries 2 fr.Sσ = cen fr.B :=
    SetLike.coe_injective ((f15a_upS_z hR hl6 hSs hSsc hz1).symm.trans (by rw [hZ2, hZB]))
  have hz2 : mset elt (cenS P C (cenE P C (closK C [1, 2, 3, 4, 5] R) (mulE P 2 4))
      [mulE P 1 3, 2, 4, 5]) = (zSeries 2 fr.Sσ : Set Γ) := by
    rw [hZB, h1b]
  have h3 := f15a_upS_z hR hl6 hSs hSsc hz2
  rw [hZ3, prodM_mset hR, hEm, hFm] at h3
  have h1c : zSeries 3 fr.Sσ = fr.E ⊔ fr.F := by
    apply le_antisymm
    · intro x hx
      have hx' : x ∈ (zSeries (2 + 1) fr.Sσ : Set Γ) := hx
      rw [← h3] at hx'
      obtain ⟨a, ha, b, hb, rfl⟩ := hx'
      exact mul_mem (mem_sup_left ha) (mem_sup_right hb)
    · refine sup_le (fun a ha => ?_) (fun b hb => ?_)
      · have : a ∈ (zSeries (2 + 1) fr.Sσ : Set Γ) := by
          rw [← h3]
          exact ⟨a, ha, 1, one_mem _, mul_one a⟩
        exact this
      · have : b ∈ (zSeries (2 + 1) fr.Sσ : Set Γ) := by
          rw [← h3]
          exact ⟨1, one_mem _, b, hb, one_mul b⟩
        exact this
  have hEFm : mset elt (prodM C (closK C [mulE P 2 4, mulE P (mulE P 1 2) 3, atR Q 2] R)
      (closK C [mulE P 1 3, mulE P 2 4, atR Q 2] R)) = ((fr.E ⊔ fr.F : Subgroup Γ) : Set Γ) := by
    rw [prodM_mset hR, hEm, hFm, h3, ← h1c]
  have h1d := f15a_secEK hR (k := 3) (by norm_num) hSs hEFm hE
  have hperm' := permB_spec hR hperm
  rw [hB, hSg] at hperm'
  have hBsm : mset elt (closK C [mulE P 1 3, 2, 4, 5, 6] R) =
      ((fr.B ⊔ closure {fr.σ} : Subgroup Γ) : Set Γ) := by
    rw [← hpr, prodM_mset hR, hB, hSg, f13_coe_sup hperm']
  have hmax := f15a_hmax hR hN hlat hSs hZB
    (fun i hi => f15a_cenE_lt (P := P) (C := C)
      (X := cenS P C (cenE P C (closK C [1, 2, 3, 4, 5] R) (mulE P 2 4)) [2, 4, 5])
      (y := mulE P 1 3) hi) hea (by rw [hkA, hAm]) (by rw [hkBs, hBsm])
  have hPA := ((hmax fr.A).2 (Or.inl rfl)).1
  have hn : ∀ t ∈ fr.Sσ, ∀ n ∈ cen fr.B, t * n * t⁻¹ ∈ cen fr.B := by
    have := f15a_normM hR hnB
    rw [hSs, hZB] at this
    exact this
  exact ⟨⟨h1a, h1b, h1c, h1d⟩, f15a_secMax (le_trans hPA.1 hPA.2.1) hn hmax,
    f15a_q8q8 hR hBsm hZm hq⟩

end CFSG.KC.G2Three.Sec1T3
