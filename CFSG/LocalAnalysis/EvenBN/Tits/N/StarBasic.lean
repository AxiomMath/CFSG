module

public import CFSG.LocalAnalysis.EvenBN.Tits.N.Generic

public section

namespace CFSG.LocalAnalysis.EvenBN.Tits.N

open Subgroup

variable {Γ : Type*} [Group Γ]

theorem actFun_of_mem (S : Subgroup Γ) {g : Γ} (hg : g ∈ normalizer (S : Set Γ)) :
    actFun S g = conjActHom S ⟨g, hg⟩ := by
  classical
  simp [actFun, hg]

theorem actFun_of_not_mem (S : Subgroup Γ) {g : Γ} (hg : g ∉ normalizer (S : Set Γ)) :
    actFun S g = 1 := by
  classical
  simp [actFun, hg]

theorem actFun_apply_coe (S : Subgroup Γ) {g : Γ} (hg : g ∈ normalizer (S : Set Γ)) (v : ↥S) :
    ((actFun S g v : ↥S) : Γ) = g * v * g⁻¹ := by
  rw [actFun_of_mem S hg]
  rfl

theorem actFun_one (S : Subgroup Γ) : actFun S 1 = 1 := by
  rw [actFun_of_mem S (one_mem _)]
  exact map_one (conjActHom S)

theorem actFun_mul (S : Subgroup Γ) {g h : Γ} (hg : g ∈ normalizer (S : Set Γ))
    (hh : h ∈ normalizer (S : Set Γ)) : actFun S (g * h) = actFun S g * actFun S h := by
  rw [actFun_of_mem S (mul_mem hg hh), actFun_of_mem S hg, actFun_of_mem S hh, ← map_mul]
  rfl

theorem actFun_inv (S : Subgroup Γ) {g : Γ} (hg : g ∈ normalizer (S : Set Γ)) :
    actFun S g⁻¹ = (actFun S g)⁻¹ := by
  rw [actFun_of_mem S (inv_mem hg), actFun_of_mem S hg, ← map_inv]
  rfl

theorem actFun_pow (S : Subgroup Γ) {g : Γ} (hg : g ∈ normalizer (S : Set Γ)) (n : ℕ) :
    actFun S (g ^ n) = actFun S g ^ n := by
  induction n with
  | zero => simpa using actFun_one S
  | succ n ih => rw [pow_succ, actFun_mul S (pow_mem hg n) hg, ih, pow_succ]

theorem actFun_conj (S : Subgroup Γ) {g h : Γ} (hg : g ∈ normalizer (S : Set Γ))
    (hh : h ∈ normalizer (S : Set Γ)) :
    actFun S (g * h * g⁻¹) = actFun S g * actFun S h * (actFun S g)⁻¹ := by
  rw [actFun_mul S (mul_mem hg hh) (inv_mem hg), actFun_mul S hg hh, actFun_inv S hg]

theorem actFun_eq_one_iff (S : Subgroup Γ) {g : Γ} (hg : g ∈ normalizer (S : Set Γ)) :
    actFun S g = 1 ↔ g ∈ centralizer (S : Set Γ) := by
  constructor
  · intro h
    rw [Subgroup.mem_centralizer_iff]
    intro v hv
    have h1 := congrArg (fun φ : MulAut ↥S => ((φ ⟨v, hv⟩ : ↥S) : Γ)) h
    simp only [actFun_apply_coe S hg, MulAut.one_apply] at h1
    exact (mul_inv_eq_iff_eq_mul.1 h1).symm
  · intro h
    ext v
    rw [actFun_apply_coe S hg, MulAut.one_apply]
    have := Subgroup.mem_centralizer_iff.1 h v v.2
    rw [mul_inv_eq_iff_eq_mul]
    exact this.symm

theorem actFun_eq_iff (S : Subgroup Γ) {g h : Γ} (hg : g ∈ normalizer (S : Set Γ))
    (hh : h ∈ normalizer (S : Set Γ)) :
    actFun S g = actFun S h ↔ g⁻¹ * h ∈ centralizer (S : Set Γ) := by
  rw [← actFun_eq_one_iff S (mul_mem (inv_mem hg) hh), actFun_mul S (inv_mem hg) hh, actFun_inv S hg,
    inv_mul_eq_one]

theorem actFun_fixes_iff (S : Subgroup Γ) {g : Γ} (hg : g ∈ normalizer (S : Set Γ)) (v : ↥S) :
    actFun S g v = v ↔ g * (v : Γ) = (v : Γ) * g := by
  rw [Subtype.ext_iff, actFun_apply_coe S hg, mul_inv_eq_iff_eq_mul]

theorem actFun_comm_of_comm (S : Subgroup Γ) {g h : Γ} (hgh : g * h = h * g) :
    actFun S g * actFun S h = actFun S h * actFun S g := by
  by_cases hg : g ∈ normalizer (S : Set Γ)
  · by_cases hh : h ∈ normalizer (S : Set Γ)
    · rw [← actFun_mul S hg hh, ← actFun_mul S hh hg, hgh]
    · rw [actFun_of_not_mem S hh, mul_one, one_mul]
  · rw [actFun_of_not_mem S hg, mul_one, one_mul]

theorem mem_imgIn_iff (S K : Subgroup Γ) {x : MulAut ↥S} :
    x ∈ imgIn S K ↔ ∃ g ∈ K, g ∈ normalizer (S : Set Γ) ∧ actFun S g = x := by
  unfold imgIn
  rw [Subgroup.mem_map]
  constructor
  · rintro ⟨g, hg, rfl⟩
    exact ⟨(g : Γ), Subgroup.mem_subgroupOf.1 hg, g.2, (actFun_of_mem S g.2).symm ▸ rfl⟩
  · rintro ⟨g, hgK, hgN, rfl⟩
    exact ⟨⟨g, hgN⟩, Subgroup.mem_subgroupOf.2 hgK, (actFun_of_mem S hgN).symm⟩

theorem actFun_mem_imgIn {S K : Subgroup Γ} {g : Γ} (hgK : g ∈ K)
    (hgN : g ∈ normalizer (S : Set Γ)) : actFun S g ∈ imgIn S K :=
  (mem_imgIn_iff S K).2 ⟨g, hgK, hgN, rfl⟩

theorem imgIn_mono (S : Subgroup Γ) {K L : Subgroup Γ} (h : K ≤ L) : imgIn S K ≤ imgIn S L := by
  intro x hx
  obtain ⟨g, hgK, hgN, rfl⟩ := (mem_imgIn_iff S K).1 hx
  exact actFun_mem_imgIn (h hgK) hgN

theorem imgIn_inf_normalizer (S K : Subgroup Γ) :
    imgIn S (K ⊓ normalizer (S : Set Γ)) = imgIn S K := by
  refine le_antisymm (imgIn_mono S inf_le_left) fun x hx => ?_
  obtain ⟨g, hgK, hgN, rfl⟩ := (mem_imgIn_iff S K).1 hx
  exact actFun_mem_imgIn (Subgroup.mem_inf.2 ⟨hgK, hgN⟩) hgN

theorem imgIn_normalizer (S : Subgroup Γ) : imgIn S (normalizer (S : Set Γ)) = (conjActHom S).range := by
  ext x
  rw [mem_imgIn_iff, MonoidHom.mem_range]
  constructor
  · rintro ⟨g, -, hgN, rfl⟩
    exact ⟨⟨g, hgN⟩, (actFun_of_mem S hgN).symm⟩
  · rintro ⟨g, rfl⟩
    exact ⟨g, g.2, g.2, actFun_of_mem S g.2⟩

theorem imgIn_le_range (S K : Subgroup Γ) : imgIn S K ≤ imgIn S (normalizer (S : Set Γ)) := by
  rw [← imgIn_inf_normalizer S K]
  exact imgIn_mono S inf_le_right

theorem mem_imgIn_normalizer_iff (S : Subgroup Γ) {x : MulAut ↥S} :
    x ∈ imgIn S (normalizer (S : Set Γ)) ↔ ∃ g ∈ normalizer (S : Set Γ), actFun S g = x := by
  rw [mem_imgIn_iff]
  exact ⟨fun ⟨g, _, hg, h⟩ => ⟨g, hg, h⟩, fun ⟨g, hg, h⟩ => ⟨g, hg, hg, h⟩⟩

theorem imgIn_eq_bot_of_le_centralizer (S : Subgroup Γ) {K : Subgroup Γ}
    (hK : K ≤ centralizer (S : Set Γ)) : imgIn S K = ⊥ := by
  refine le_bot_iff.1 fun x hx => ?_
  obtain ⟨g, hgK, hgN, rfl⟩ := (mem_imgIn_iff S K).1 hx
  rw [(actFun_eq_one_iff S hgN).2 (hK hgK)]
  exact one_mem _

theorem imgIn_sup_of_le (S : Subgroup Γ) {K L : Subgroup Γ} (hK : K ≤ normalizer (S : Set Γ))
    (hL : L ≤ normalizer (S : Set Γ)) : imgIn S (K ⊔ L) = imgIn S K ⊔ imgIn S L := by
  have hKL : K ⊔ L ≤ normalizer (S : Set Γ) := sup_le hK hL
  unfold imgIn
  rw [← Subgroup.map_sup, ← Subgroup.subgroupOf_sup hK hL]

theorem imgIn_map_conj (S K : Subgroup Γ) {g : Γ} (hg : g ∈ normalizer (S : Set Γ)) :
    imgIn S (K.map (MulAut.conj g).toMonoidHom) =
      (imgIn S K).map (MulAut.conj (actFun S g)).toMonoidHom := by
  ext x
  rw [mem_imgIn_iff, Subgroup.mem_map]
  constructor
  · rintro ⟨h, hh, hhN, rfl⟩
    obtain ⟨k, hk, rfl⟩ := Subgroup.mem_map.1 hh
    have hkN : k ∈ normalizer (S : Set Γ) := by
      have := mul_mem (mul_mem (inv_mem hg) hhN) hg
      simpa [MulAut.conj_apply, mul_assoc] using this
    refine ⟨actFun S k, actFun_mem_imgIn hk hkN, ?_⟩
    simp only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply]
    exact (actFun_conj S hg hkN).symm
  · rintro ⟨y, hy, rfl⟩
    obtain ⟨k, hk, hkN, rfl⟩ := (mem_imgIn_iff S K).1 hy
    refine ⟨g * k * g⁻¹, Subgroup.mem_map.2 ⟨k, hk, rfl⟩,
      mul_mem (mul_mem hg hkN) (inv_mem hg), ?_⟩
    simp only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply]
    exact actFun_conj S hg hkN

theorem imgIn_inf_centralizer_le (S K : Subgroup Γ) (g : Γ) :
    imgIn S (K ⊓ centralizer ({g} : Set Γ)) ≤
      centralizer ({actFun S g} : Set (MulAut ↥S)) ⊓ imgIn S K := by
  intro x hx
  refine Subgroup.mem_inf.2 ⟨?_, imgIn_mono S inf_le_left hx⟩
  obtain ⟨k, hk, hkN, rfl⟩ := (mem_imgIn_iff S _).1 hx
  rw [Subgroup.mem_centralizer_singleton_iff]
  have hkg := Subgroup.mem_centralizer_singleton_iff.1 (Subgroup.mem_inf.1 hk).2
  exact actFun_comm_of_comm S hkg

theorem imgIn_commutator (S : Subgroup Γ) {K L : Subgroup Γ} (hK : K ≤ normalizer (S : Set Γ))
    (hL : L ≤ normalizer (S : Set Γ)) : imgIn S ⁅K, L⁆ = ⁅imgIn S K, imgIn S L⁆ := by
  have hKL : ⁅K, L⁆ ≤ normalizer (S : Set Γ) :=
    Subgroup.commutator_le.2 fun a ha b hb => by
      rw [commutatorElement_def]
      exact mul_mem (mul_mem (mul_mem (hK ha) (hL hb)) (inv_mem (hK ha))) (inv_mem (hL hb))
  unfold imgIn
  rw [← Subgroup.map_commutator]
  congr 1
  have h1 := Subgroup.map_subgroupOf_eq_of_le hK
  have h2 := Subgroup.map_subgroupOf_eq_of_le hL
  have h3 := Subgroup.map_subgroupOf_eq_of_le hKL
  apply Subgroup.map_injective (Subgroup.subtype_injective (normalizer (S : Set Γ)))
  rw [h3, Subgroup.map_commutator, h1, h2]

theorem mem_preIn_iff (S : Subgroup Γ) (K' : Subgroup (MulAut ↥S)) {g : Γ} :
    g ∈ preIn S K' ↔ g ∈ normalizer (S : Set Γ) ∧ actFun S g ∈ K' := by
  unfold preIn
  rw [Subgroup.mem_map]
  constructor
  · rintro ⟨x, hx, rfl⟩
    refine ⟨x.2, ?_⟩
    change actFun S (x : Γ) ∈ K'
    rw [actFun_of_mem S x.2]
    exact hx
  · rintro ⟨hgN, hg⟩
    exact ⟨⟨g, hgN⟩, by rw [Subgroup.mem_comap, ← actFun_of_mem S hgN]; exact hg, rfl⟩

theorem preIn_le_normalizer (S : Subgroup Γ) (K' : Subgroup (MulAut ↥S)) :
    preIn S K' ≤ normalizer (S : Set Γ) := fun _ hg => ((mem_preIn_iff S K').1 hg).1

theorem centralizer_le_preIn (S : Subgroup Γ) (K' : Subgroup (MulAut ↥S)) :
    centralizer (S : Set Γ) ≤ preIn S K' := by
  intro g hg
  have hgN : g ∈ normalizer (S : Set Γ) := Subgroup.centralizer_le_normalizer _ hg
  exact (mem_preIn_iff S K').2 ⟨hgN, by rw [(actFun_eq_one_iff S hgN).2 hg]; exact one_mem _⟩

theorem preIn_mono (S : Subgroup Γ) {K L : Subgroup (MulAut ↥S)} (h : K ≤ L) : preIn S K ≤ preIn S L :=
  fun _ hg => (mem_preIn_iff S L).2 ⟨((mem_preIn_iff S K).1 hg).1, h ((mem_preIn_iff S K).1 hg).2⟩

theorem preIn_inf (S : Subgroup Γ) (K L : Subgroup (MulAut ↥S)) :
    preIn S (K ⊓ L) = preIn S K ⊓ preIn S L := by
  ext g
  simp only [Subgroup.mem_inf, mem_preIn_iff]
  tauto

theorem imgIn_preIn (S : Subgroup Γ) (K' : Subgroup (MulAut ↥S)) :
    imgIn S (preIn S K') = K' ⊓ imgIn S (normalizer (S : Set Γ)) := by
  ext x
  rw [Subgroup.mem_inf, mem_imgIn_iff, mem_imgIn_normalizer_iff]
  constructor
  · rintro ⟨g, hg, hgN, rfl⟩
    exact ⟨((mem_preIn_iff S K').1 hg).2, g, hgN, rfl⟩
  · rintro ⟨hx, g, hgN, rfl⟩
    exact ⟨g, (mem_preIn_iff S K').2 ⟨hgN, hx⟩, hgN, rfl⟩

theorem imgIn_preIn_of_le (S : Subgroup Γ) {K' : Subgroup (MulAut ↥S)}
    (hK' : K' ≤ imgIn S (normalizer (S : Set Γ))) : imgIn S (preIn S K') = K' := by
  rw [imgIn_preIn]
  exact inf_eq_left.2 hK'

theorem mem_normalizer_preIn_iff (S : Subgroup Γ) {K' : Subgroup (MulAut ↥S)}
    (hK' : K' ≤ imgIn S (normalizer (S : Set Γ))) {g : Γ} (hg : g ∈ normalizer (S : Set Γ)) :
    g ∈ normalizer ((preIn S K' : Subgroup Γ) : Set Γ) ↔
      actFun S g ∈ normalizer (K' : Set (MulAut ↥S)) := by
  have forward : ∀ g : Γ, g ∈ normalizer (S : Set Γ) → g ∈ normalizer ((preIn S K' : Subgroup Γ) : Set Γ) →
      ∀ y ∈ K', actFun S g * y * (actFun S g)⁻¹ ∈ K' := by
    intro g hgN hgP y hy
    obtain ⟨x, hxN, rfl⟩ := (mem_imgIn_normalizer_iff S).1 (hK' hy)
    have hxP : x ∈ preIn S K' := (mem_preIn_iff S K').2 ⟨hxN, hy⟩
    have := ((mem_preIn_iff S K').1 ((Subgroup.mem_normalizer_iff.1 hgP x).1 hxP)).2
    rwa [actFun_conj S hgN hxN] at this
  constructor
  · intro hgP
    rw [Subgroup.mem_normalizer_iff]
    intro y
    refine ⟨forward g hg hgP y, fun hy => ?_⟩
    have h2 := forward g⁻¹ (inv_mem hg) (inv_mem hgP) _ hy
    rw [actFun_inv S hg] at h2
    simpa [mul_assoc] using h2
  · intro hgK
    rw [Subgroup.mem_normalizer_iff]
    intro x
    rw [mem_preIn_iff, mem_preIn_iff]
    have hxN : g * x * g⁻¹ ∈ normalizer (S : Set Γ) ↔ x ∈ normalizer (S : Set Γ) := by
      constructor
      · intro h
        have := mul_mem (mul_mem (inv_mem hg) h) hg
        simpa [mul_assoc] using this
      · intro h
        exact mul_mem (mul_mem hg h) (inv_mem hg)
    constructor
    · rintro ⟨hx, hxK⟩
      refine ⟨hxN.2 hx, ?_⟩
      rw [actFun_conj S hg hx]
      exact (Subgroup.mem_normalizer_iff.1 hgK _).1 hxK
    · rintro ⟨hgx, hgxK⟩
      have hx := hxN.1 hgx
      refine ⟨hx, ?_⟩
      rw [actFun_conj S hg hx] at hgxK
      exact (Subgroup.mem_normalizer_iff.1 hgK _).2 hgxK

theorem centralizer_act_le_imgIn_of_transitive (S : Subgroup Γ) {t : Γ}
    (ht : t ∈ normalizer (S : Set Γ))
    (htrans : ∀ h ∈ normalizer (S : Set Γ), (h * t * h⁻¹)⁻¹ * t ∈ centralizer (S : Set Γ) →
      ∃ c ∈ centralizer (S : Set Γ), c * (h * t * h⁻¹) * c⁻¹ = t) :
    centralizer ({actFun S t} : Set (MulAut ↥S)) ⊓ imgIn S (normalizer (S : Set Γ)) ≤
      imgIn S (centralizer ({t} : Set Γ)) := by
  intro x hx
  obtain ⟨hxC, hxR⟩ := Subgroup.mem_inf.1 hx
  obtain ⟨h, hhN, rfl⟩ := (mem_imgIn_normalizer_iff S).1 hxR
  have hcomm := Subgroup.mem_centralizer_singleton_iff.1 hxC
  have hconj : actFun S (h * t * h⁻¹) = actFun S t := by
    rw [actFun_conj S hhN ht, hcomm, mul_inv_cancel_right]
  obtain ⟨c, hc, hct⟩ := htrans h hhN
    ((actFun_eq_iff S (mul_mem (mul_mem hhN ht) (inv_mem hhN)) ht).1 hconj)
  have hcN : c ∈ normalizer (S : Set Γ) := Subgroup.centralizer_le_normalizer _ hc
  refine (mem_imgIn_iff S _).2 ⟨c * h, ?_, mul_mem hcN hhN, ?_⟩
  · rw [Subgroup.mem_centralizer_singleton_iff]
    have h1 : c * h * t * (c * h)⁻¹ = c * (h * t * h⁻¹) * c⁻¹ := by group
    exact (mul_inv_eq_iff_eq_mul.1 (h1.trans hct))
  · rw [actFun_mul S hcN hhN, (actFun_eq_one_iff S hcN).2 hc, one_mul]

theorem card_imgIn_mul_card [Finite Γ] (S K : Subgroup Γ) :
    Nat.card (imgIn S K) * Nat.card (K ⊓ centralizer (S : Set Γ) : Subgroup Γ) =
      Nat.card (K ⊓ normalizer (S : Set Γ) : Subgroup Γ) := by
  classical
  let ψ : ↥(K ⊓ normalizer (S : Set Γ)) →* MulAut ↥S :=
    (conjActHom S).comp (Subgroup.inclusion
      (inf_le_right : K ⊓ normalizer (S : Set Γ) ≤ normalizer (S : Set Γ)))
  have hrange : ψ.range = imgIn S K := by
    rw [← imgIn_inf_normalizer S K]
    simp only [ψ, MonoidHom.range_comp, Subgroup.inclusion_range]
    rfl
  have hker : ψ.ker = (K ⊓ centralizer (S : Set Γ)).subgroupOf (K ⊓ normalizer (S : Set Γ)) := by
    ext x
    rw [MonoidHom.mem_ker, Subgroup.mem_subgroupOf, Subgroup.mem_inf]
    have hxN : (x : Γ) ∈ normalizer (S : Set Γ) := (Subgroup.mem_inf.1 x.2).2
    have hψ : ψ x = actFun S (x : Γ) := by
      rw [actFun_of_mem S hxN]
      rfl
    rw [hψ, actFun_eq_one_iff S hxN]
    constructor
    · intro h
      exact ⟨(Subgroup.mem_inf.1 x.2).1, h⟩
    · intro h
      exact h.2
  have hcard := Subgroup.card_ker_mul_card_range ψ
  rw [hker, hrange] at hcard
  have hle : (K ⊓ centralizer (S : Set Γ)) ≤ K ⊓ normalizer (S : Set Γ) :=
    inf_le_inf_left K (Subgroup.centralizer_le_normalizer _)
  rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe hle).toEquiv] at hcard
  rw [mul_comm]
  exact hcard

theorem card_imgIn_dvd [Finite Γ] (S K : Subgroup Γ) :
    Nat.card (imgIn S K) ∣ Nat.card (K ⊓ normalizer (S : Set Γ) : Subgroup Γ) :=
  Dvd.intro _ (card_imgIn_mul_card S K)

theorem isPGroup_imgIn {p : ℕ} (S : Subgroup Γ) {K : Subgroup Γ} (hK : IsPGroup p K) :
    IsPGroup p (imgIn S K) := by
  intro y
  obtain ⟨g, hgK, hgN, hy⟩ := (mem_imgIn_iff S K).1 y.2
  obtain ⟨n, hn⟩ := hK ⟨g, hgK⟩
  refine ⟨n, Subtype.ext ?_⟩
  have h1 : g ^ (p ^ n) = 1 := congrArg Subtype.val hn
  rw [Subgroup.coe_pow, ← hy, ← actFun_pow S hgN, h1, actFun_one]
  rfl

theorem isElemAbelian_imgIn {p : ℕ} (S : Subgroup Γ) {K : Subgroup Γ}
    (hK : CFSG.Open.IsElemAbelian p K) : CFSG.Open.IsElemAbelian p (imgIn S K) := by
  refine ⟨⟨⟨fun a b => ?_⟩⟩, fun x hx => ?_⟩
  · obtain ⟨g, hgK, hgN, ha⟩ := (mem_imgIn_iff S K).1 a.2
    obtain ⟨h, hhK, hhN, hb⟩ := (mem_imgIn_iff S K).1 b.2
    apply Subtype.ext
    have hc : g * h = h * g := by
      have := hK.1.1.comm ⟨g, hgK⟩ ⟨h, hhK⟩
      simpa using congrArg Subtype.val this
    show (a : MulAut ↥S) * b = b * a
    rw [← ha, ← hb]
    exact actFun_comm_of_comm S hc
  · obtain ⟨g, hgK, hgN, rfl⟩ := (mem_imgIn_iff S K).1 hx
    rw [← actFun_pow S hgN, hK.2 g hgK, actFun_one]

theorem actFun_eq_one_of_mem_of_comm (S : Subgroup Γ) (hS : ∀ a ∈ S, ∀ b ∈ S, a * b = b * a) {g : Γ}
    (hg : g ∈ S) : actFun S g = 1 := by
  have hgN : g ∈ normalizer (S : Set Γ) := Subgroup.le_normalizer hg
  exact (actFun_eq_one_iff S hgN).2 (Subgroup.mem_centralizer_iff.2 fun v hv => (hS v hv g hg))

end CFSG.LocalAnalysis.EvenBN.Tits.N
