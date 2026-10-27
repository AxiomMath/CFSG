module

public import CFSG.LocalAnalysis.QuasithinUnique.GammaFamiliesConfining
public import CFSG.LocalAnalysis.QuasithinUnique.Ch1.L239ListedA7OverK

public section

namespace CFSG.QuasithinUnique.Vol2Native.L239

namespace A7Over

open CFSG.Open

abbrev Alt7 := alternatingGroup (Fin 7)

section Finite

def sigmaZero : Equiv.Perm (Fin 7) := Equiv.swap 0 1 * Equiv.swap 2 3 * Equiv.swap 4 5

def centSet : Finset (Equiv.Perm (Fin 7)) :=
  Finset.univ.filter (fun a => a * sigmaZero = sigmaZero * a ∧ Equiv.Perm.sign a = 1)

def kleinSet : Finset (Equiv.Perm (Fin 7)) :=
  {1, Equiv.swap 0 1 * Equiv.swap 2 3, Equiv.swap 0 1 * Equiv.swap 4 5,
    Equiv.swap 2 3 * Equiv.swap 4 5}

set_option maxRecDepth 100000 in
theorem centSet_card : centSet.card = 24 := by
  rw [centSet]
  exact L239K.card_K (by decide +kernel)

set_option maxRecDepth 100000 in
theorem centSet_not_klein : ∀ y ∈ centSet, y ∉ kleinSet →
    ∃ c ∈ centSet, (y * (c * y * c⁻¹)) ^ 8 ≠ 1 := by
  intro y hy hk
  rw [centSet, Finset.mem_filter] at hy
  have hk' : ¬ (y = 1 ∨ y = Equiv.swap 0 1 * Equiv.swap 2 3 ∨ y = Equiv.swap 0 1 * Equiv.swap 4 5 ∨
      y = Equiv.swap 2 3 * Equiv.swap 4 5) := by
    intro h
    apply hk
    simp only [kleinSet, Finset.mem_insert, Finset.mem_singleton]
    exact h
  obtain ⟨c, hc, hc8⟩ := L239K.not_klein_K (s := sigmaZero) (by decide +kernel) (by decide +kernel)
    (by decide +kernel) (by decide +kernel) (by decide +kernel) y hy.2 hk'
  refine ⟨c, ?_, hc8⟩
  rw [centSet, Finset.mem_filter]
  exact ⟨Finset.mem_univ _, hc⟩

set_option maxRecDepth 100000 in
theorem klein_conj : ∀ y ∈ kleinSet, y ≠ 1 → ∀ v ∈ kleinSet, v ≠ 1 →
    ∃ c ∈ centSet, c * y * c⁻¹ = v := by
  have key : ∀ x ∈ kleinSet, x ≠ 1 → x ∈ [Equiv.swap 0 1 * Equiv.swap 2 3,
      Equiv.swap 0 1 * Equiv.swap 4 5, Equiv.swap 2 3 * Equiv.swap 4 5] := by
    intro x hx hx1
    simp only [kleinSet, Finset.mem_insert, Finset.mem_singleton] at hx
    rcases hx with rfl | rfl | rfl | rfl
    · exact absurd rfl hx1
    all_goals simp
  intro y hy hy1 v hv hv1
  obtain ⟨c, hc, hcv⟩ := L239K.conj_K (s := sigmaZero) (by decide +kernel) (by decide +kernel) y
    (key y hy hy1) v (key v hv hv1)
  refine ⟨c, ?_, hcv⟩
  rw [centSet, Finset.mem_filter]
  exact ⟨Finset.mem_univ _, hc⟩

set_option maxRecDepth 100000 in
theorem klein_mul : ∀ x ∈ kleinSet, ∀ y ∈ kleinSet, x * y ∈ kleinSet := by
  have hk : ∀ z, z ∈ kleinSet ↔ z ∈ [1, Equiv.swap 0 1 * Equiv.swap 2 3,
      Equiv.swap 0 1 * Equiv.swap 4 5, Equiv.swap 2 3 * Equiv.swap 4 5] := by
    intro z
    simp only [kleinSet, Finset.mem_insert, Finset.mem_singleton, List.mem_cons, List.not_mem_nil,
      or_false]
  intro x hx y hy
  rw [hk] at hx hy ⊢
  exact (L239K.klein_K (by decide +kernel)).1 x hx y hy

set_option maxRecDepth 100000 in
theorem klein_inv : ∀ x ∈ kleinSet, x⁻¹ ∈ kleinSet := by
  have hk : ∀ z, z ∈ kleinSet ↔ z ∈ [1, Equiv.swap 0 1 * Equiv.swap 2 3,
      Equiv.swap 0 1 * Equiv.swap 4 5, Equiv.swap 2 3 * Equiv.swap 4 5] := by
    intro z
    simp only [kleinSet, Finset.mem_insert, Finset.mem_singleton, List.mem_cons, List.not_mem_nil,
      or_false]
  intro x hx
  rw [hk] at hx ⊢
  exact (L239K.klein_K (by decide +kernel)).2.1 x hx

set_option maxRecDepth 100000 in
theorem klein_card : kleinSet.card = 4 := by decide +kernel

set_option maxRecDepth 100000 in
theorem klein_sign : ∀ x ∈ kleinSet, Equiv.Perm.sign x = 1 := by
  have hk : ∀ z, z ∈ kleinSet ↔ z ∈ [1, Equiv.swap 0 1 * Equiv.swap 2 3,
      Equiv.swap 0 1 * Equiv.swap 4 5, Equiv.swap 2 3 * Equiv.swap 4 5] := by
    intro z
    simp only [kleinSet, Finset.mem_insert, Finset.mem_singleton, List.mem_cons, List.not_mem_nil,
      or_false]
  intro x hx
  rw [hk] at hx
  exact (L239K.klein_K (by decide +kernel)).2.2 x hx

theorem sigmaZero_cycleType : sigmaZero.cycleType = {2, 2, 2} := by
  have hd : Equiv.Perm.Disjoint (Equiv.swap (0 : Fin 7) 1 * Equiv.swap 2 3) (Equiv.swap 4 5) :=
    Equiv.Perm.Disjoint.mul_left (Equiv.Perm.disjoint_swap_swap (by decide))
      (Equiv.Perm.disjoint_swap_swap (by decide))
  rw [sigmaZero, hd.cycleType_mul, Equiv.Perm.cycleType_swap_mul_swap_of_nodup (by decide),
    Equiv.Perm.isSwap_iff_cycleType.mp (Equiv.Perm.swap_isSwap_iff.mpr (by decide))]
  rfl

end Finite

section Subgroups

@[expose] def centSub (σ : Equiv.Perm (Fin 7)) : Subgroup Alt7 :=
  (Subgroup.centralizer ({σ} : Set (Equiv.Perm (Fin 7)))).comap Alt7.subtype

theorem mem_centSub (σ : Equiv.Perm (Fin 7)) (x : Alt7) :
    x ∈ centSub σ ↔ (x : Equiv.Perm (Fin 7)) * σ = σ * (x : Equiv.Perm (Fin 7)) := by
  show (x : Equiv.Perm (Fin 7)) ∈ Subgroup.centralizer ({σ} : Set (Equiv.Perm (Fin 7))) ↔ _
  exact Subgroup.mem_centralizer_singleton_iff

abbrev centZero : Subgroup Alt7 := centSub sigmaZero

theorem mem_centZero (x : Alt7) : x ∈ centZero ↔ (x : Equiv.Perm (Fin 7)) ∈ centSet := by
  have h2 : Equiv.Perm.sign (x : Equiv.Perm (Fin 7)) = 1 := Equiv.Perm.mem_alternatingGroup.mp x.2
  refine (mem_centSub sigmaZero x).trans ?_
  simp [centSet, h2]

def kleinZero : Subgroup Alt7 where
  carrier := {x | (x : Equiv.Perm (Fin 7)) ∈ kleinSet}
  mul_mem' := fun {_ _} ha hb => klein_mul _ ha _ hb
  one_mem' := by decide +kernel
  inv_mem' := fun {_} ha => klein_inv _ ha

theorem card_centZero : Nat.card centZero = 24 := by
  rw [← centSet_card, ← Nat.card_eq_finsetCard]
  refine Nat.card_congr ?_
  exact
    { toFun := fun x => ⟨(x.1 : Equiv.Perm (Fin 7)), (mem_centZero x.1).mp x.2⟩
      invFun := fun p => ⟨⟨p.1, Equiv.Perm.mem_alternatingGroup.mpr (Finset.mem_filter.mp p.2).2.2⟩,
        (mem_centZero _).mpr p.2⟩
      left_inv := fun _ => rfl
      right_inv := fun _ => rfl }

theorem card_kleinZero : Nat.card kleinZero = 4 := by
  rw [← klein_card, ← Nat.card_eq_finsetCard]
  refine Nat.card_congr ?_
  exact
    { toFun := fun x => ⟨(x.1 : Equiv.Perm (Fin 7)), x.2⟩
      invFun := fun p => ⟨⟨p.1, Equiv.Perm.mem_alternatingGroup.mpr (klein_sign _ p.2)⟩, p.2⟩
      left_inv := fun _ => rfl
      right_inv := fun _ => rfl }

theorem card_dvd_eight {Q : Subgroup Alt7} (hQ : IsPGroup 2 Q) : Nat.card Q ∣ 8 := by
  have hcard : Nat.card Alt7 = 2520 := by
    rw [Nat.card_eq_fintype_card, card_alternatingGroup]
    simp [Nat.factorial]
  obtain ⟨n, hn⟩ := hQ.exists_card_eq
  have hdvd : Nat.card Q ∣ 2520 := hcard ▸ Subgroup.card_subgroup_dvd_card Q
  rw [hn] at hdvd ⊢
  have hcop : Nat.Coprime (2 ^ n) 315 := Nat.Coprime.pow_left n (by norm_num)
  exact hcop.dvd_of_dvd_mul_right (by simpa using hdvd)

theorem pow_eight_of_isPGroup {Q : Subgroup Alt7} (hQ : IsPGroup 2 Q) (w : Alt7) (hw : w ∈ Q) :
    w ^ 8 = 1 := by
  have : orderOf (⟨w, hw⟩ : Q) ∣ 8 := (orderOf_dvd_natCard _).trans (card_dvd_eight hQ)
  have h1 : (⟨w, hw⟩ : Q) ^ 8 = 1 := orderOf_dvd_iff_pow_eq_one.mp this
  simpa using congrArg Subtype.val h1

theorem normal_two_subgroup_eq {Q : Subgroup Alt7} (hQC : Q ≤ centZero)
    (hN : centZero ≤ Subgroup.normalizer (Q : Set Alt7)) (hQ2 : IsPGroup 2 Q) (hQ1 : Q ≠ ⊥) :
    Q = kleinZero := by
  have hconj : ∀ c ∈ centZero, ∀ q ∈ Q, c * q * c⁻¹ ∈ Q := fun c hc q hq =>
    (Subgroup.mem_normalizer_iff.mp (hN hc) q).mp hq
  have hQV : Q ≤ kleinZero := by
    intro x hx
    by_contra hxV
    have hxs : (x : Equiv.Perm (Fin 7)) ∈ centSet := (mem_centZero x).mp (hQC hx)
    obtain ⟨c, hc, hne⟩ := centSet_not_klein _ hxs hxV
    let c' : Alt7 := ⟨c, Equiv.Perm.mem_alternatingGroup.mpr (Finset.mem_filter.mp hc).2.2⟩
    have hc' : c' ∈ centZero := (mem_centZero c').mpr hc
    have hw : x * (c' * x * c'⁻¹) ∈ Q := Q.mul_mem hx (hconj c' hc' x hx)
    have h8 := pow_eight_of_isPGroup hQ2 _ hw
    apply hne
    simpa using congrArg (fun a : Alt7 => (a : Equiv.Perm (Fin 7))) h8
  refine le_antisymm hQV ?_
  obtain ⟨y, hy1⟩ := (Subgroup.ne_bot_iff_exists_ne_one).mp hQ1
  have hyV : (y : Alt7) ∈ kleinZero := hQV y.2
  have hy1' : (y : Equiv.Perm (Fin 7)) ≠ 1 := by
    intro h
    apply hy1
    apply Subtype.ext
    apply Subtype.ext
    simpa using h
  intro v hv
  by_cases hv1 : (v : Equiv.Perm (Fin 7)) = 1
  · have : v = 1 := by
      apply Subtype.ext
      simpa using hv1
    rw [this]
    exact Q.one_mem
  · obtain ⟨c, hc, hcv⟩ := klein_conj _ hyV hy1' _ hv hv1
    let c' : Alt7 := ⟨c, Equiv.Perm.mem_alternatingGroup.mpr (Finset.mem_filter.mp hc).2.2⟩
    have hc' : c' ∈ centZero := (mem_centZero c').mpr hc
    have : c' * (y : Alt7) * c'⁻¹ = v := by
      apply Subtype.ext
      simpa using hcv
    rw [← this]
    exact hconj c' hc' _ y.2

theorem a7_core {G : Type} [Group G] [Finite G] (C V Y : Subgroup G)
    (hCY : C ≤ Y) (hCcard : Nat.card C = 24) (hVcard : Nat.card V = 4)
    (hVY : Y ≤ Subgroup.normalizer (V : Set G))
    (hcent : Y ⊓ Subgroup.centralizer (V : Set G) ≤ V) : Y = C := by
  classical
  have hconj : ∀ y ∈ Y, ∀ v ∈ V, y * v * y⁻¹ ∈ V := fun y hy v hv =>
    (Subgroup.mem_normalizer_iff.mp (hVY hy) v).mp hv
  let X := {v : ↥V // v ≠ 1}
  have hXcard : Nat.card X = 3 := by
    have : Fintype V := Fintype.ofFinite V
    have h4 : Fintype.card V = 4 := by rw [← Nat.card_eq_fintype_card]; exact hVcard
    have h1 := Fintype.card_subtype_compl (fun x : V => x = 1)
    have h2 : Fintype.card {x : V // x = 1} = 1 := Fintype.card_subtype_eq 1
    have h3 : Fintype.card {x : V // ¬ x = 1} = Fintype.card {v : V // v ≠ 1} := rfl
    rw [Nat.card_eq_fintype_card]
    show Fintype.card {v : V // v ≠ 1} = 3
    omega
  let act : ↥Y → X → X := fun y x =>
    ⟨⟨(y : G) * (x.1 : G) * (y : G)⁻¹, hconj y y.2 x.1 x.1.2⟩, by
      intro h
      apply x.2
      apply Subtype.ext
      have h' : (y : G) * (x.1 : G) * (y : G)⁻¹ = 1 := congrArg Subtype.val h
      have h'' : (x.1 : G) = 1 := by
        have := congrArg (fun w => (y : G)⁻¹ * w * (y : G)) h'
        simpa [mul_assoc] using this
      exact h''⟩
  have act_one : ∀ x, act 1 x = x := by
    intro x
    apply Subtype.ext
    apply Subtype.ext
    simp [act]
  have act_mul : ∀ y y' x, act (y * y') x = act y (act y' x) := by
    intro y y' x
    apply Subtype.ext
    apply Subtype.ext
    simp [act, mul_assoc]
  let φ : ↥Y →* Equiv.Perm X :=
    { toFun := fun y =>
        { toFun := act y
          invFun := act y⁻¹
          left_inv := fun x => by rw [← act_mul, inv_mul_cancel, act_one]
          right_inv := fun x => by rw [← act_mul, mul_inv_cancel, act_one] }
      map_one' := Equiv.ext act_one
      map_mul' := fun y y' => Equiv.ext (act_mul y y') }
  have hker : φ.ker ≤ (Y ⊓ Subgroup.centralizer (V : Set G)).subgroupOf Y := by
    intro y hy
    rw [MonoidHom.mem_ker] at hy
    rw [Subgroup.mem_subgroupOf]
    have hc : (y : G) ∈ Subgroup.centralizer (V : Set G) := by
      rw [Subgroup.mem_centralizer_iff]
      intro v hv
      by_cases hv1 : (⟨v, hv⟩ : V) = 1
      · have : v = 1 := congrArg Subtype.val hv1
        subst this
        simp
      · have h1 : act y ⟨⟨v, hv⟩, hv1⟩ = ⟨⟨v, hv⟩, hv1⟩ := by
          have := congrArg (fun p : Equiv.Perm X => p ⟨⟨v, hv⟩, hv1⟩) hy
          simpa [φ] using this
        have h2 : (y : G) * v * (y : G)⁻¹ = v := congrArg (fun w : X => ((w.1 : V) : G)) h1
        calc v * (y : G) = ((y : G) * v * (y : G)⁻¹) * (y : G) := by rw [h2]
          _ = (y : G) * v := by group
    exact ⟨y.2, hc⟩
  have hkcard : Nat.card φ.ker ≤ 4 := by
    calc Nat.card φ.ker ≤ Nat.card ((Y ⊓ Subgroup.centralizer (V : Set G)).subgroupOf Y) :=
          Subgroup.card_le_of_le hker
      _ = Nat.card (Y ⊓ Subgroup.centralizer (V : Set G) : Subgroup G) :=
          Nat.card_congr (Subgroup.subgroupOfEquivOfLe inf_le_left).toEquiv
      _ ≤ Nat.card V := Subgroup.card_le_of_le hcent
      _ = 4 := hVcard
  have hidx : φ.ker.index ≤ 6 := by
    rw [Subgroup.index_ker]
    calc Nat.card φ.range ≤ Nat.card (Equiv.Perm X) := Subgroup.card_le_card_group _
      _ = 6 := by rw [Nat.card_perm, hXcard]; rfl
  have hYcard : Nat.card Y ≤ 24 := by
    rw [← Subgroup.card_mul_index φ.ker]
    calc Nat.card φ.ker * φ.ker.index ≤ 4 * 6 := Nat.mul_le_mul hkcard hidx
      _ = 24 := by norm_num
  exact (Subgroup.eq_of_le_of_card_ge hCY (by rw [hCcard]; exact hYcard)).symm

theorem a7_sigma0 (Y : Subgroup Alt7) (hCY : centZero ≤ Y) (Q : Subgroup Alt7) (hQ2 : IsPGroup 2 Q)
    (hQY : Y ≤ Subgroup.normalizer (Q : Set Alt7))
    (hcent : Y ⊓ Subgroup.centralizer (Q : Set Alt7) ≤ Q) (hQC : Q ≤ centZero) :
    Y = centZero := by
  have hQ1 : Q ≠ ⊥ := by
    intro hQ
    have hY : Y ≤ ⊥ := by
      intro y hy
      have hyc : y ∈ Subgroup.centralizer (Q : Set Alt7) := by
        rw [Subgroup.mem_centralizer_iff]
        intro h hh
        rw [hQ] at hh
        have : h = 1 := hh
        rw [this]
        simp
      have := hcent ⟨hy, hyc⟩
      rwa [hQ] at this
    have h1 : Nat.card centZero ≤ Nat.card Y := Subgroup.card_le_of_le hCY
    have h2 : Nat.card Y ≤ Nat.card (⊥ : Subgroup Alt7) := Subgroup.card_le_of_le hY
    rw [card_centZero, Subgroup.card_bot] at *
    omega
  have hQV : Q = kleinZero := normal_two_subgroup_eq hQC (hCY.trans hQY) hQ2 hQ1
  subst hQV
  exact a7_core centZero kleinZero Y hCY card_centZero card_kleinZero hQY hcent

end Subgroups

section Glue

theorem pCoreOf_le_centZero {Y : Subgroup Alt7} (hCY : centZero ≤ Y) :
    pCoreOf 2 Y ≤ centZero := by
  obtain ⟨T, hT⟩ := exists_isSylowTwoOf centZero
  have hT8 : Nat.card T = 8 := by
    rw [hT.card_eq]
    show 2 ^ (Nat.card centZero).factorization 2 = 8
    rw [card_centZero]
    have h : Nat.factorization 24 2 = 3 := by decide +kernel
    rw [h]
    norm_num
  obtain ⟨P, hTP, hP⟩ := exists_isSylowTwoOf_of_le (hT.le.trans hCY) hT.isPGroup
  have hP8 : Nat.card P ≤ 8 := Nat.le_of_dvd (by norm_num) (card_dvd_eight hP.isPGroup)
  have hTP' : T = P := Subgroup.eq_of_le_of_card_ge hTP (by rw [hT8]; exact hP8)
  subst hTP'
  exact hP.pCoreOf_le.trans hT.le

theorem sigmaZero_case {Y : Subgroup Alt7} (hCY : centZero ≤ Y) (hY : CharTwo Y) :
    Y = centZero :=
  a7_sigma0 Y hCY (pCoreOf 2 Y) (CFSG.RankThreeCoreUniqueness.Helpers.pCoreOf_isPGroup 2 Y)
    (CFSG.RankThreeCoreUniqueness.Helpers.localGroup_le_normalizer_pCoreOf 2 Y) hY
    (pCoreOf_le_centZero hCY)

theorem charTwo_map_equiv {Y : Subgroup Alt7} (hY : CharTwo Y) (e : Alt7 ≃* Alt7) :
    CharTwo (Y.map e.toMonoidHom) :=
  charTwo_iff_internal.mpr
    (CFSG.RankThreeCoreUniqueness.Helpers.self_centralizing_pCore_of_mulEquiv 2
      (Subgroup.equivMapOfInjective Y e.toMonoidHom e.injective) (charTwo_iff_internal.mp hY))

theorem general {σ : Equiv.Perm (Fin 7)} (hσ : σ.cycleType = {2, 2, 2}) {Y : Subgroup Alt7}
    (hCY : centSub σ ≤ Y) (hY : CharTwo Y) : Y = centSub σ := by
  obtain ⟨g, hg⟩ : ∃ g : Equiv.Perm (Fin 7), g * sigmaZero * g⁻¹ = σ :=
    isConj_iff.mp (Equiv.Perm.isConj_iff_cycleType_eq.mpr (by rw [hσ, sigmaZero_cycleType]))
  let e : Alt7 ≃* Alt7 := MulAut.conjNormal (H := alternatingGroup (Fin 7)) g⁻¹
  have he : ∀ x : Alt7, ((e x : Alt7) : Equiv.Perm (Fin 7)) = g⁻¹ * (x : Equiv.Perm (Fin 7)) * g := by
    intro x
    simp only [e, MulAut.conjNormal_apply, inv_inv]
  let e' : Alt7 ≃* Alt7 := MulAut.conjNormal (H := alternatingGroup (Fin 7)) g
  have he' : ∀ x : Alt7, ((e' x : Alt7) : Equiv.Perm (Fin 7)) = g * (x : Equiv.Perm (Fin 7)) * g⁻¹ := by
    intro x
    simp only [e', MulAut.conjNormal_apply]
  have hee' : ∀ x : Alt7, e (e' x) = x := by
    intro x
    apply Subtype.ext
    rw [he, he']
    group
  have hmem : ∀ x : Alt7, x ∈ centSub σ ↔ e x ∈ centZero := by
    intro x
    rw [mem_centSub, mem_centSub, he]
    constructor
    · intro h
      calc g⁻¹ * (x : Equiv.Perm (Fin 7)) * g * sigmaZero
          = g⁻¹ * ((x : Equiv.Perm (Fin 7)) * (g * sigmaZero * g⁻¹)) * g := by group
        _ = g⁻¹ * ((g * sigmaZero * g⁻¹) * (x : Equiv.Perm (Fin 7))) * g := by rw [hg, h]
        _ = sigmaZero * (g⁻¹ * (x : Equiv.Perm (Fin 7)) * g) := by group
    · intro h
      calc (x : Equiv.Perm (Fin 7)) * σ
          = g * (g⁻¹ * (x : Equiv.Perm (Fin 7)) * g * sigmaZero) * g⁻¹ := by rw [← hg]; group
        _ = g * (sigmaZero * (g⁻¹ * (x : Equiv.Perm (Fin 7)) * g)) * g⁻¹ := by rw [h]
        _ = σ * (x : Equiv.Perm (Fin 7)) := by rw [← hg]; group
  have hC' : centZero ≤ Y.map e.toMonoidHom := by
    intro x hx
    refine ⟨e' x, hCY ((hmem (e' x)).mpr ?_), hee' x⟩
    rw [hee']
    exact hx
  have hY' : Y.map e.toMonoidHom = centZero :=
    sigmaZero_case hC' (charTwo_map_equiv hY e)
  refine le_antisymm (fun y hy => ?_) hCY
  rw [hmem]
  have : e y ∈ Y.map e.toMonoidHom := ⟨y, hy, rfl⟩
  rwa [hY'] at this

end Glue

end A7Over

end CFSG.QuasithinUnique.Vol2Native.L239
