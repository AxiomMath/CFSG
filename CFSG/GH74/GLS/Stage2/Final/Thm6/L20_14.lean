module

public import CFSG.GH74.GLS.Stage2.Final.Thm6.L20_14Core
public import CFSG.GH74.GLS.Stage2.Final.Thm6.L20_14Layer
public import CFSG.GroupTheory.ABGLocalTools.CoreLemmas
public import CFSG.GH74.GLS.Stage2.Final.Thm6.L20_14Diag
public import CFSG.GH74.GLS.Stage2.Final.Thm6.Lemmas2

public section

namespace CFSG.GH74.GLS.Stage2.Final.Thm6.L20

open Subgroup CFSG CFSG.LocalCores CFSG.GH74 CFSG.GH74.GLS CFSG.GH74.GLS.Bg CFSG.GH74.GLS.Stage2.Local
  CFSG.GH74.GLS.Stage2.Final.Thm4
open scoped commutatorElement

variable {G : Type} [Group G]

variable {G : Type} [Group G]

theorem mem_conjugate_iff {H : Subgroup G} {g x : G} : x ∈ conjugate H g ↔ g * x * g⁻¹ ∈ H := by
  unfold conjugate
  rw [Subgroup.mem_map_equiv]
  simp

theorem Cen_zc_eq (z g : G) : Cen (zc z g) = conjugate (Cen z) g := by
  ext x
  rw [mem_conjugate_iff, Subgroup.mem_centralizer_singleton_iff, Subgroup.mem_centralizer_singleton_iff]
  unfold zc
  constructor
  · intro h
    calc g * x * g⁻¹ * z = g * (x * (g⁻¹ * z * g)) * g⁻¹ := by group
      _ = g * ((g⁻¹ * z * g) * x) * g⁻¹ := by rw [h]
      _ = z * (g * x * g⁻¹) := by group
  · intro h
    calc x * (g⁻¹ * z * g) = g⁻¹ * (g * x * g⁻¹ * z) * g := by group
      _ = g⁻¹ * (z * (g * x * g⁻¹)) * g := by rw [h]
      _ = (g⁻¹ * z * g) * x := by group

theorem isCoatom_conjugate {K : Subgroup G} (hK : IsCoatom K) (g : G) : IsCoatom (conjugate K g) := by
  refine ⟨fun htop => hK.1 ?_, fun b hb => ?_⟩
  · rw [eq_top_iff]
    intro y _
    have : g⁻¹ * y * g ∈ conjugate K g := by rw [htop]; trivial
    rw [mem_conjugate_iff] at this
    have e : g * (g⁻¹ * y * g) * g⁻¹ = y := by group
    rwa [e] at this
  · set b' : Subgroup G := b.comap (MulAut.conj g⁻¹).toMonoidHom with hb'
    have hmem : ∀ w, w ∈ b' ↔ g⁻¹ * w * g ∈ b := by
      intro w; simp [hb']
    have hKb' : K < b' := by
      refine lt_of_le_of_ne (fun k hk => ?_) (fun heq => ?_)
      · rw [hmem]
        apply hb.le
        rw [mem_conjugate_iff]
        simpa [mul_assoc] using hk
      · obtain ⟨x, hxb, hxn⟩ := Set.exists_of_ssubset hb
        have : g * x * g⁻¹ ∈ b' := by rw [hmem]; simpa [mul_assoc] using hxb
        rw [← heq] at this
        exact hxn (mem_conjugate_iff.mpr this)
    have htop := hK.2 _ hKb'
    rw [eq_top_iff]
    intro y _
    have : g * y * g⁻¹ ∈ b' := by rw [htop]; trivial
    rw [hmem] at this
    simpa [mul_assoc] using this

section Odd

variable [Finite G] {z : G} {K₁ K₂ : Subgroup G} {L₁ L₂ : Subgroup (CentralizerBar z)}

theorem oddA_z (hK : CompData z K₁ K₂ L₁ L₂) {y : G} (hyC : y ∈ Cen z) (hy2 : y * y = 1)
    (hsw : cj (toBar z ⟨y, hyC⟩) L₁ = L₂) {x : G} (hxC : x ∈ Cen z) (hodd : Odd (orderOf x))
    (hxI : x ∈ centralizer (Em ((K₁ ⊔ K₂) ⊓ centralizer ({y} : Set G)) : Set G)) : x ∈ OddCore z := by
  obtain ⟨hs₁, hs₂⟩ := hK.swap y hyC hsw
  have hI : ∀ a ∈ K₁, a * (y * a * y⁻¹) ∈ Em ((K₁ ⊔ K₂) ⊓ centralizer ({y} : Set G)) := by
    intro a ha
    exact diag_le_layer hK.quasi₁ hK.comm hy2 hs₁ hs₂ ⟨⟨a, ha⟩, rfl⟩
  obtain ⟨hn₁, hn₂⟩ := hK.odd_norm x hxC hodd
  obtain ⟨h1, h2⟩ := diag_centralizes hK.perf₁ hK.comm hy2 hs₁ hs₂ hI hn₁ hn₂
    (fun i hi => (Subgroup.mem_centralizer_iff.mp hxI i hi).symm)
  exact hK.odd_mem x hxC hodd h1 h2

theorem oddA_y (hK : CompData z K₁ K₂ L₁ L₂) {g : G} (hz2 : z * z = 1) (hyC : zc z g ∈ Cen z)
    (hy2 : zc z g * zc z g = 1) (hsw : cj (toBar z ⟨zc z g, hyC⟩) L₁ = L₂)
    (htC : g * z * g⁻¹ ∈ Cen z) (htsw : cj (toBar z ⟨g * z * g⁻¹, htC⟩) L₁ = L₂)
    {x : G} (hxC : x ∈ Cen (zc z g)) (hodd : Odd (orderOf x))
    (hxI : x ∈ centralizer (Em ((K₁ ⊔ K₂) ⊓ centralizer ({zc z g} : Set G)) : Set G)) :
    x ∈ conjugate (OddCore z) g := by
  set y := zc z g with hy
  set t := g * z * g⁻¹ with ht
  set I := Em ((K₁ ⊔ K₂) ⊓ centralizer ({y} : Set G)) with hI
  obtain ⟨hs₁, hs₂⟩ := hK.swap y hyC hsw
  obtain ⟨ht₁, ht₂⟩ := hK.swap t htC htsw
  have ht2 : t * t = 1 := by
    calc t * t = g * (z * z) * g⁻¹ := by simp only [ht]; group
      _ = 1 := by rw [hz2]; group
  have hx₀C : g * x * g⁻¹ ∈ Cen z := by
    have := (mem_conjugate_iff (H := Cen z) (g := g) (x := x)).mp (by rw [← Cen_zc_eq]; exact hxC)
    exact this
  have hx₀odd : Odd (orderOf (g * x * g⁻¹)) := by
    have : orderOf (g * x * g⁻¹) = orderOf x := by
      have := MulEquiv.orderOf_eq (MulAut.conj g) x
      simpa using this
    rwa [this]
  set K₁' := conjugate K₁ g with hK₁'
  set K₂' := conjugate K₂ g with hK₂'
  have hcen' : ∀ b ∈ K₁' ⊔ K₂', b ∈ Cen y := by
    intro b hb
    have hle : K₁' ⊔ K₂' ≤ Cen y := by
      rw [Cen_zc_eq]
      refine sup_le (fun b hb => ?_) (fun b hb => ?_)
      · rw [mem_conjugate_iff] at hb ⊢; exact hK.le₁ hb
      · rw [mem_conjugate_iff] at hb ⊢; exact hK.le₂ hb
    exact hle hb
  have hs₁' : ∀ b ∈ K₁', z * b * z⁻¹ ∈ K₂' := by
    intro b hb
    rw [mem_conjugate_iff] at hb ⊢
    have e : g * (z * b * z⁻¹) * g⁻¹ = t * (g * b * g⁻¹) * t⁻¹ := by simp only [ht]; group
    rw [e]; exact ht₁ _ hb
  have hs₂' : ∀ b ∈ K₂', z * b * z⁻¹ ∈ K₁' := by
    intro b hb
    rw [mem_conjugate_iff] at hb ⊢
    have e : g * (z * b * z⁻¹) * g⁻¹ = t * (g * b * g⁻¹) * t⁻¹ := by simp only [ht]; group
    rw [e]; exact ht₂ _ hb
  have hc' : ∀ b ∈ K₁', ∀ b' ∈ K₂', b * b' = b' * b := by
    intro b hb b' hb'
    rw [mem_conjugate_iff] at hb hb'
    have := hK.comm _ hb _ hb'
    have e : g * (b * b') * g⁻¹ = (g * b * g⁻¹) * (g * b' * g⁻¹) := by group
    have e' : g * (b' * b) * g⁻¹ = (g * b' * g⁻¹) * (g * b * g⁻¹) := by group
    have h3 : g * (b * b') * g⁻¹ = g * (b' * b) * g⁻¹ := by rw [e, e', this]
    simpa using h3
  set δ' := diagHom K₁' K₂' z hs₁' hc' with hδ'
  have hperf' : ⁅K₁', K₁'⁆ = K₁' := by
    show ⁅K₁.map _, K₁.map _⁆ = K₁.map _
    rw [← Subgroup.map_commutator, hK.perf₁]
  have hperfΔ : ⁅δ'.range, δ'.range⁆ = δ'.range := by
    have hp : Group.IsPerfect ↥K₁' := Subgroup.isPerfect_iff.mpr hperf'
    rw [MonoidHom.range_eq_map, ← Subgroup.map_commutator]
    have := hp.commutator_eq_top
    rw [commutator_def] at this
    rw [this]
  have hΔC : δ'.range ≤ Cen z := by
    rintro _ ⟨b, rfl⟩
    exact (Subgroup.mem_inf.mp (diagHom_mem hc' hz2 hs₁' b)).2
  have hΔL : δ'.range ≤ K₁ ⊔ K₂ := by
    have := hK.perfect δ'.range hΔC hperfΔ
    rwa [hK.layer] at this
  have hΔy : ∀ p ∈ δ'.range, y * p * y⁻¹ = p := by
    rintro _ ⟨b, rfl⟩
    have hp : δ' b ∈ Cen y := hcen' _ (diagHom_mem_sup hc' hs₁' b)
    have h3 := Subgroup.mem_centralizer_singleton_iff.mp hp
    calc y * δ' b * y⁻¹ = (δ' b * y) * y⁻¹ := by rw [← h3]
      _ = δ' b := by group
  have hΔI : δ'.range ≤ I :=
    (perfect_le_diag hK.comm hs₁ hs₂ hperfΔ hΔL hΔy).trans
      (diag_le_layer hK.quasi₁ hK.comm hy2 hs₁ hs₂)
  have hI₀ : ∀ a ∈ K₁, a * (t * a * t⁻¹) ∈ I.map (MulAut.conj g).toMonoidHom := by
    intro a ha
    have hb : g⁻¹ * a * g ∈ K₁' := by
      rw [mem_conjugate_iff]
      have e : g * (g⁻¹ * a * g) * g⁻¹ = a := by group
      rwa [e]
    have hmem := hΔI ⟨⟨g⁻¹ * a * g, hb⟩, rfl⟩
    refine ⟨g⁻¹ * a * g * (z * (g⁻¹ * a * g) * z⁻¹), hmem, ?_⟩
    show g * (g⁻¹ * a * g * (z * (g⁻¹ * a * g) * z⁻¹)) * g⁻¹ = a * (t * a * t⁻¹)
    simp only [ht]
    group
  obtain ⟨hn₁, hn₂⟩ := hK.odd_norm _ hx₀C hx₀odd
  obtain ⟨h1, h2⟩ := diag_centralizes hK.perf₁ hK.comm ht2 ht₁ ht₂ hI₀ hn₁ hn₂ (by
    rintro _ ⟨i, hi, rfl⟩
    have := (Subgroup.mem_centralizer_iff.mp hxI i hi).symm
    show g * x * g⁻¹ * (g * i * g⁻¹) = (g * i * g⁻¹) * (g * x * g⁻¹)
    calc g * x * g⁻¹ * (g * i * g⁻¹) = g * (x * i) * g⁻¹ := by group
      _ = g * (i * x) * g⁻¹ := by rw [this]
      _ = g * i * g⁻¹ * (g * x * g⁻¹) := by group)
  have hxA := hK.odd_mem _ hx₀C hx₀odd h1 h2
  rw [mem_conjugate_iff]
  exact hxA

end Odd

theorem conjugate_conjugate_inv (B : Subgroup G) (g : G) : conjugate (conjugate B g) g⁻¹ = B := by
  ext x
  rw [mem_conjugate_iff, mem_conjugate_iff]
  have e : g * (g⁻¹ * x * g⁻¹⁻¹) * g⁻¹ = x := by group
  simp [mul_assoc]

section OpConj

variable [Finite G]

theorem Op_ne_bot_conjugate (r : ℕ) {B : Subgroup G} (g : G) (h : Op r B ≠ ⊥) :
    Op r (conjugate B g) ≠ ⊥ := by
  intro hbot
  apply h
  have hWle : conjugate (Op r B) g ≤ conjugate B g := by
    intro w hw
    rw [mem_conjugate_iff] at hw ⊢
    exact (Subgroup.map_subtype_le _) hw
  have hWn : ∀ b ∈ conjugate B g, ∀ w ∈ conjugate (Op r B) g, b * w * b⁻¹ ∈ conjugate (Op r B) g := by
    intro b hb w hw
    rw [mem_conjugate_iff] at hb hw ⊢
    have hn := Op_conj_mem (C := B) r (fun c hc b hb => B.mul_mem (B.mul_mem hc hb) (B.inv_mem hc)) hb hw
    have e : g * (b * w * b⁻¹) * g⁻¹ = (g * b * g⁻¹) * (g * w * g⁻¹) * (g * b * g⁻¹)⁻¹ := by group
    rw [e]; exact hn
  have hWp : IsPGroup r (conjugate (Op r B) g) :=
    (isPGroup_Op r B).of_equiv (Subgroup.equivMapOfInjective _ _ (MulAut.conj g⁻¹).injective)
  have hW := le_Op_of_normalized r hWle hWn hWp
  rw [hbot] at hW
  rw [eq_bot_iff]
  intro x hx
  have h1 : g⁻¹ * x * g ∈ conjugate (Op r B) g := by
    rw [mem_conjugate_iff]
    have e : g * (g⁻¹ * x * g) * g⁻¹ = x := by group
    rwa [e]
  have h2 := hW h1
  rw [Subgroup.mem_bot] at h2
  have : x = 1 := by
    have e : x = g * (g⁻¹ * x * g) * g⁻¹ := by group
    rw [e, h2]; group
  rw [this]; exact Subgroup.one_mem _

theorem Op_ne_bot_of_conjugate (r : ℕ) {B : Subgroup G} (g : G) (h : Op r (conjugate B g) ≠ ⊥) :
    Op r B ≠ ⊥ := by
  have := Op_ne_bot_conjugate r g⁻¹ h
  rwa [conjugate_conjugate_inv] at this

end OpConj

theorem exists_mem_conj_into_sylow [Finite G] {K S : Subgroup G} (hS : CFSG.ABGLocalTools.IsSylowOf 2 S K)
    {t : G} (htK : t ∈ K) (ht2 : t * t = 1) : ∃ c ∈ K, c * t * c⁻¹ ∈ S := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  set t' : ↥K := ⟨t, htK⟩ with ht'
  have ht'2 : t' * t' = 1 := Subtype.ext ht2
  have hord : orderOf t' ∣ 2 := orderOf_dvd_of_pow_eq_one (by rw [sq]; exact ht'2)
  have hp : IsPGroup 2 (Subgroup.zpowers t') := by
    refine IsPGroup.of_card (n := if orderOf t' = 1 then 0 else 1) ?_
    rw [Nat.card_zpowers]
    rcases (Nat.dvd_prime Nat.prime_two).mp hord with h | h
    · simp [h]
    · simp [h]
  obtain ⟨Q, hQ⟩ := hp.exists_le_sylow
  have hP' : CFSG.ABGLocalTools.IsSylowOf 2 ((Q : Subgroup ↥K).map K.subtype) K := ⟨Q, rfl⟩
  obtain ⟨k, hkK, hk⟩ := hS.exists_mem_conj hP'
  refine ⟨k⁻¹, K.inv_mem hkK, ?_⟩
  have htP : t ∈ (Q : Subgroup ↥K).map K.subtype := ⟨t', hQ (Subgroup.mem_zpowers t'), rfl⟩
  have := (hk t).mp htP
  simpa using this

section IyConj

variable [Finite G] {z : G} {K₁ K₂ : Subgroup G} {L₁ L₂ : Subgroup (CentralizerBar z)}

theorem Iy_le_conj (hK : CompData z K₁ K₂ L₁ L₂) (g : G) :
    Em ((K₁ ⊔ K₂) ⊓ centralizer ({zc z g} : Set G)) ≤ conjugate (K₁ ⊔ K₂) g := by
  set D := (K₁ ⊔ K₂) ⊓ centralizer ({zc z g} : Set G) with hD
  set P := Em D with hP
  have hPD : P ≤ D := Subgroup.map_subtype_le _
  have hPperf : ⁅P, P⁆ = P := by
    show ⁅(layer ↥D).map D.subtype, (layer ↥D).map D.subtype⁆ = (layer ↥D).map D.subtype
    rw [← Subgroup.map_commutator, layer_perfect]
  set P₀ := P.map (MulAut.conj g).toMonoidHom with hP₀
  have hP₀C : P₀ ≤ Cen z := by
    rintro _ ⟨p, hp, rfl⟩
    have h1 := Subgroup.mem_centralizer_singleton_iff.mp (Subgroup.mem_inf.mp (hPD hp)).2
    rw [Subgroup.mem_centralizer_singleton_iff]
    show g * p * g⁻¹ * z = z * (g * p * g⁻¹)
    unfold zc at h1
    calc g * p * g⁻¹ * z = g * (p * (g⁻¹ * z * g)) * g⁻¹ := by group
      _ = g * ((g⁻¹ * z * g) * p) * g⁻¹ := by rw [h1]
      _ = z * (g * p * g⁻¹) := by group
  have hP₀perf : ⁅P₀, P₀⁆ = P₀ := by
    rw [hP₀, ← Subgroup.map_commutator, hPperf]
  have h1 := hK.perfect P₀ hP₀C hP₀perf
  rw [hK.layer] at h1
  intro p hp
  rw [mem_conjugate_iff]
  exact h1 ⟨p, hp, rfl⟩

end IyConj

section Main

variable [Finite G] {z : G} {K₁ K₂ : Subgroup G} {L₁ L₂ : Subgroup (CentralizerBar z)}

theorem Op_le_F20 (r : ℕ) [Fact r.Prime] (z : G) : Op r (OddCore z) ≤ F20 z :=
  Subgroup.map_mono (pCore_le_fitting _ r)

theorem odd_orderOf_of_mem_Op {r : ℕ} (hr : r.Prime) (hr2 : r ≠ 2) {B : Subgroup G} {x : G} (hx : x ∈ Op r B) :
    Odd (orderOf x) := by
  have : Fact r.Prime := ⟨hr⟩
  obtain ⟨k, hk⟩ := (isPGroup_Op r B) ⟨x, hx⟩
  have hdvd : orderOf x ∣ r ^ k := by
    apply orderOf_dvd_of_pow_eq_one
    have := congrArg Subtype.val hk
    simpa using this
  obtain ⟨j, -, hj⟩ := (Nat.dvd_prime_pow hr).mp hdvd
  rw [hj]
  exact Odd.pow (hr.odd_of_ne_two hr2)

theorem prime_step (hK : CompData z K₁ K₂ L₁ L₂) (hz2 : z * z = 1) (hcoat : IsCoatom (Cen z))
    (hsimple : ∀ N : Subgroup G, N.Normal → N = ⊥ ∨ N = ⊤) {g : G}
    (hyC : zc z g ∈ Cen z) (hsw : cj (toBar z ⟨zc z g, hyC⟩) L₁ = L₂)
    (htC : g * z * g⁻¹ ∈ Cen z) (htsw : cj (toBar z ⟨g * z * g⁻¹, htC⟩) L₁ = L₂)
    (h12c : ∀ f ∈ F20 z, zc z g * f * (zc z g)⁻¹ = f⁻¹) {r : ℕ} (hr : r.Prime) (hr2 : r ≠ 2) :
    (∀ x ∈ Op r (Fm (Hy z g)), x ∈ Cen z → x = 1) ∧ (∀ x ∈ Op r (Fm (Hy z g)), x ∈ Cen (zc z g) → x = 1) := by
  have : Fact r.Prime := ⟨hr⟩
  set y := zc z g with hy
  have hy2 : y * y = 1 := by
    calc y * y = g⁻¹ * (z * z) * g := by simp only [hy, zc]; group
      _ = 1 := by rw [hz2]; group
  have hIy : Iy z g = Em ((K₁ ⊔ K₂) ⊓ centralizer ({y} : Set G)) := by
    unfold Iy L20; rw [hK.layer]
  have hIL : Iy z g ≤ Em (Cen z) := by
    refine (Subgroup.map_subtype_le _).trans ?_
    exact inf_le_left
  set H := Hy z g with hH
  set X := Op r (Fm H) with hX
  have hXH : ∀ h ∈ H, ∀ x ∈ X, h * x * h⁻¹ ∈ X := fun h hh x hx =>
    Op_conj_mem r (fun c hc b hb => Fm_conj_mem H hc hb) hh hx
  have hXp : IsPGroup r X := isPGroup_Op r (Fm H)
  have hXHle : X ≤ H := (Subgroup.map_subtype_le _).trans (Subgroup.map_subtype_le _)
  have hxHI : ∀ x ∈ X, x ∈ centralizer (Em ((K₁ ⊔ K₂) ⊓ centralizer ({y} : Set G)) : Set G) := by
    intro x hx
    have := hXHle hx
    rw [hH, Hy, hIy] at this
    exact this
  have hBC_z : OddCore z ≤ Cen z := Subgroup.map_subtype_le _
  have hBnorm_z : ∀ c ∈ Cen z, ∀ b ∈ OddCore z, c * b * c⁻¹ ∈ OddCore z := fun c hc b hb =>
    (Subgroup.mem_normalizer_iff.mp
      (le_normalizer_map_subtype (Cen z) (pPrimeCore 2 ↥(Cen z)) hc) b).mp hb
  have hBH_z : OddCore z ≤ H := by
    intro a ha
    rw [hH, Hy]
    refine Subgroup.mem_centralizer_iff.mpr fun i hi => ?_
    exact (hK.oddcomm a ha i (hIL hi)).symm
  have hz := core_growth (Ĉ := Cen z) (B := OddCore z) (H := H) (X := X) r hcoat hsimple hBC_z
    hBnorm_z hBH_z hXH hXp (fun x hx hxC =>
      oddA_z hK hyC hy2 hsw hxC (odd_orderOf_of_mem_Op hr hr2 hx) (hxHI x hx))
  have hcoat_y : IsCoatom (Cen y) := by rw [hy, Cen_zc_eq]; exact isCoatom_conjugate hcoat g
  have hBC_y : Ag z g ≤ Cen y := by
    intro a ha
    rw [hy, Cen_zc_eq, mem_conjugate_iff]
    exact hBC_z (mem_conjugate_iff.mp ha)
  have hBnorm_y : ∀ c ∈ Cen y, ∀ b ∈ Ag z g, c * b * c⁻¹ ∈ Ag z g := by
    intro c hc b hb
    rw [hy, Cen_zc_eq, mem_conjugate_iff] at hc
    have hb' := mem_conjugate_iff.mp hb
    show c * b * c⁻¹ ∈ conjugate (OddCore z) g
    rw [mem_conjugate_iff]
    have e : g * (c * b * c⁻¹) * g⁻¹ = (g * c * g⁻¹) * (g * b * g⁻¹) * (g * c * g⁻¹)⁻¹ := by group
    rw [e]
    exact hBnorm_z _ hc _ hb'
  have hBH_y : Ag z g ≤ H := by
    intro a ha
    rw [hH, Hy]
    refine Subgroup.mem_centralizer_iff.mpr fun i hi => ?_
    have hi' : g * i * g⁻¹ ∈ K₁ ⊔ K₂ := mem_conjugate_iff.mp (Iy_le_conj hK g (hIy ▸ hi))
    have hcomm := hK.oddcomm (g * a * g⁻¹) (mem_conjugate_iff.mp ha) (g * i * g⁻¹) (by rwa [hK.layer])
    have e1 : i * a = g⁻¹ * ((g * i * g⁻¹) * (g * a * g⁻¹)) * g := by group
    have e2 : a * i = g⁻¹ * ((g * a * g⁻¹) * (g * i * g⁻¹)) * g := by group
    rw [e1, e2, hcomm]
  have hy' := core_growth (Ĉ := Cen y) (B := Ag z g) (H := H) (X := X) r hcoat_y hsimple hBC_y
    hBnorm_y hBH_y hXH hXp (fun x hx hxC =>
      oddA_y hK hz2 hyC hy2 hsw htC htsw hxC (odd_orderOf_of_mem_Op hr hr2 hx) (hxHI x hx))
  have hzero : ∀ x ∈ X, (x ∈ Cen z → x = 1) ∧ (x ∈ Cen y → x = 1) := by
    rcases hz with ⟨hA0, hX0⟩ | ⟨hA1, hXA⟩ <;> rcases hy' with ⟨hAg0, hXg0⟩ | ⟨hAg1, hXAg⟩
    · intro x hx
      exact ⟨fun hxC => Subgroup.mem_bot.mp (hX0 ▸ (⟨hx, hxC⟩ : x ∈ X ⊓ Cen z)),
        fun hxC => Subgroup.mem_bot.mp (hXg0 ▸ (⟨hx, hxC⟩ : x ∈ X ⊓ Cen y))⟩
    · exact absurd hA0 (Op_ne_bot_of_conjugate r g hAg1)
    · exact absurd hAg0 (Op_ne_bot_conjugate r g hA1)
    · intro x hx
      have hxF : x ∈ F20 z := Op_le_F20 r z (hXA hx)
      have hxAg : x ∈ Ag z g := Subgroup.map_subtype_le _ (hXAg hx)
      have hxCy : x ∈ Cen y := hBC_y hxAg
      have h1 := h12c x hxF
      have h2 : y * x * y⁻¹ = x := by
        have := Subgroup.mem_centralizer_singleton_iff.mp hxCy
        calc y * x * y⁻¹ = (x * y) * y⁻¹ := by rw [this]
          _ = x := by group
      have hxx : x * x = 1 := mul_eq_one_iff_eq_inv.mpr (h2.symm.trans h1)
      have hodd := odd_orderOf_of_mem_Op hr hr2 hx
      have hx1 : x = 1 := by
        have hd : orderOf x ∣ 2 := orderOf_dvd_of_pow_eq_one (by rw [sq]; exact hxx)
        rcases (Nat.dvd_prime Nat.prime_two).mp hd with h | h
        · exact orderOf_eq_one_iff.mp h
        · rw [h] at hodd; exact absurd hodd (by decide)
      exact ⟨fun _ => hx1, fun _ => hx1⟩
  exact ⟨fun x hx hxC => (hzero x hx).1 hxC, fun x hx hxC => (hzero x hx).2 hxC⟩

theorem concl20_14_of_good (hK : CompData z K₁ K₂ L₁ L₂) (hz2 : z * z = 1) (hcoat : IsCoatom (Cen z))
    (hsimple : ∀ N : Subgroup G, N.Normal → N = ⊥ ∨ N = ⊤) {g : G}
    (hyC : zc z g ∈ Cen z) (hsw : cj (toBar z ⟨zc z g, hyC⟩) L₁ = L₂)
    (htC : g * z * g⁻¹ ∈ Cen z) (htsw : cj (toBar z ⟨g * z * g⁻¹, htC⟩) L₁ = L₂)
    (h12c : ∀ f ∈ F20 z, zc z g * f * (zc z g)⁻¹ = f⁻¹) : Concl20_14 z g := by
  set y := zc z g with hy
  have hy2 : y * y = 1 := by
    calc y * y = g⁻¹ * (z * z) * g := by simp only [hy, zc]; group
      _ = 1 := by rw [hz2]; group
  have hIL : Iy z g ≤ Em (Cen z) := by
    refine (Subgroup.map_subtype_le _).trans ?_
    exact inf_le_left
  have hzH : z ∈ Hy z g := by
    rw [Hy]
    refine Subgroup.mem_centralizer_iff.mpr fun i hi => ?_
    have := Subgroup.mem_centralizer_singleton_iff.mp ((Subgroup.map_subtype_le _ (hIL hi) : i ∈ Cen z))
    exact this
  have hyH : y ∈ Hy z g := by
    rw [Hy]
    refine Subgroup.mem_centralizer_iff.mpr fun i hi => ?_
    have hiy : i ∈ L20 z ⊓ centralizer ({y} : Set G) := Subgroup.map_subtype_le _ hi
    have := Subgroup.mem_centralizer_singleton_iff.mp (Subgroup.mem_inf.mp hiy).2
    exact this
  have hprime := fun r hr hr2 => prime_step hK hz2 hcoat hsimple hyC hsw htC htsw h12c (r := r) hr hr2
  have hz : ∀ e ∈ Ey z g, z * e * z⁻¹ = e⁻¹ :=
    Fpi_odd_inverted hzH hz2 (fun r hr hr2 x hx hxz => (hprime r hr hr2).1 x hx (by
      rw [Subgroup.mem_centralizer_singleton_iff]
      calc x * z = (z * x * z⁻¹) * z := by rw [hxz]
        _ = z * x := by group))
  have hy' : ∀ e ∈ Ey z g, y * e * y⁻¹ = e⁻¹ :=
    Fpi_odd_inverted hyH hy2 (fun r hr hr2 x hx hxy => (hprime r hr hr2).2 x hx (by
      rw [Subgroup.mem_centralizer_singleton_iff]
      calc x * y = (y * x * y⁻¹) * y := by rw [hxy]
        _ = y * x := by group))
  intro e he
  refine ⟨hy' e he, hz e he, ?_⟩
  have h1 := hy' e he
  have h2 := hz e he
  calc (y * z) * e = y * (z * e * z⁻¹) * z := by group
    _ = y * e⁻¹ * z := by rw [h2]
    _ = (y * e * y⁻¹)⁻¹ * (y * z) := by group
    _ = e * (y * z) := by rw [h1]; group

omit [Finite G] in
theorem swaps_cj {z y : G} {L₁ L₂ : Subgroup (CentralizerBar z)} (hsw : Swaps z y L₁ L₂) :
    ∃ hy : y ∈ Cen z, cj (toBar z ⟨y, hy⟩) L₁ = L₂ := by
  obtain ⟨hy, h1, h2⟩ := hsw
  refine ⟨hy, ?_⟩
  rw [← h2]
  show cj _ (cj _ L₂) = L₂
  rw [cj_cj, mul_inv_cancel, cj_one]

end Main

end CFSG.GH74.GLS.Stage2.Final.Thm6.L20

namespace CFSG.GH74.GLS.Stage2.Final.Thm6

open Subgroup CFSG CFSG.LocalCores CFSG.GH74 CFSG.GH74.GLS CFSG.GH74.GLS.Bg CFSG.GH74.GLS.Stage2.Local
  CFSG.GH74.GLS.Stage2.Final.Thm4 CFSG.GH74.GLS.Stage2.Final.Thm6.L20

theorem lemma20_14_thm (h12 : Lemma20_12) : Lemma20_14 := by
  intro G _ _ z k S M h hMC hpsp g hS
  subst hMC
  have hctx : Stage2Ctx G z k S := h.ctx.ctx17.ctx
  have hSC : S ≤ Cen z := hctx.S_le_Cen
  have hz2 : z * z = 1 := by
    have := hctx.orderOf_z
    calc z * z = z ^ 2 := (sq z).symm
      _ = 1 := by rw [← this]; exact pow_orderOf_eq_one z
  have hcoat : IsCoatom (Cen z) := h.ctx.ctx17.mem.1
  have hsimple : ∀ N : Subgroup G, N.Normal → N = ⊥ ∨ N = ⊤ := fun N hN =>
    hctx.std.kps.1.eq_bot_or_eq_top_of_normal N
  have h4a : pLayerOf 2 (Cen z) = Em (Cen z) := h.ctx.thm4.1
  obtain ⟨q, L₁, L₂, hpair, hswap⟩ := hS.swap
  obtain ⟨q', hk, L₁', L₂', hpsp4⟩ := hpsp
  have hT : TypeCl z k S := Or.inr ⟨q', hk, L₁', L₂', hpsp4⟩
  obtain ⟨-, h12b, h12c⟩ := h12 G z k S (Cen z) h rfl hT
  obtain ⟨K₁, K₂, hK⟩ := exists_compData hpair h4a
  have hyS : zc z g ∈ S := hS.y_mem
  have hyC : zc z g ∈ Cen z := hSC hyS
  have hy2 : zc z g * zc z g = 1 := by
    calc zc z g * zc z g = g⁻¹ * (z * z) * g := by simp only [zc]; group
      _ = 1 := by rw [hz2]; group
  have hyconj : IsConj z (zc z g) := isConj_iff.mpr ⟨g⁻¹, by simp [zc]⟩
  have hyne : zc z g ≠ z := by
    intro hyz
    obtain ⟨hy, hsw⟩ := swaps_cj hswap
    have hcen : toBar z ⟨zc z g, hy⟩ ∈ center (CentralizerBar z) := by
      have := toBar_z_mem_center z
      have e : (⟨zc z g, hy⟩ : ↥(Cen z)) = ⟨z, mem_Cen_self z⟩ := Subtype.ext hyz
      rwa [e]
    have hfix : cj (toBar z ⟨zc z g, hy⟩) L₁ = L₁ :=
      cj_eq_iff.mpr (Subgroup.center_le_normalizer (L₁ : Set (CentralizerBar z)) hcen)
    exact hpair.ne (hfix.symm.trans hsw)
  have htC : g * z * g⁻¹ ∈ Cen z := by
    rw [Subgroup.mem_centralizer_singleton_iff]
    have h1 := Subgroup.mem_centralizer_singleton_iff.mp hyC
    simp only [zc] at h1
    calc g * z * g⁻¹ * z = g * (z * (g⁻¹ * z * g)) * g⁻¹ := by group
      _ = g * ((g⁻¹ * z * g) * z) * g⁻¹ := by rw [← h1]
      _ = z * (g * z * g⁻¹) := by group
  have ht2 : (g * z * g⁻¹) * (g * z * g⁻¹) = 1 := by
    calc (g * z * g⁻¹) * (g * z * g⁻¹) = g * (z * z) * g⁻¹ := by group
      _ = 1 := by rw [hz2]; group
  obtain ⟨c, hcC, hc⟩ := exists_mem_conj_into_sylow hctx.sylow htC ht2
  set g₁ := c * g with hg₁
  have hzc : zc z g₁ = zc z g := by
    have h1 := Subgroup.mem_centralizer_singleton_iff.mp hcC
    simp only [zc, hg₁]
    calc (c * g)⁻¹ * z * (c * g) = g⁻¹ * (c⁻¹ * z * c) * g := by group
      _ = g⁻¹ * z * g := by
        have : c⁻¹ * z * c = z := by
          calc c⁻¹ * z * c = c⁻¹ * (z * c) := by group
            _ = c⁻¹ * (c * z) := by rw [h1]
            _ = z := by group
        rw [this]
  have hyC₁ : zc z g₁ ∈ Cen z := by rw [hzc]; exact hyC
  have hsw₁ : cj (toBar z ⟨zc z g₁, hyC₁⟩) L₁ = L₂ := by
    obtain ⟨hy, hsw⟩ := swaps_cj hswap
    have e : (⟨zc z g₁, hyC₁⟩ : ↥(Cen z)) = ⟨zc z g, hy⟩ := Subtype.ext hzc
    rwa [e]
  have ht₁S : g₁ * z * g₁⁻¹ ∈ S := by
    have e : g₁ * z * g₁⁻¹ = c * (g * z * g⁻¹) * c⁻¹ := by simp only [hg₁]; group
    rwa [e]
  have ht₁C : g₁ * z * g₁⁻¹ ∈ Cen z := hSC ht₁S
  have ht₁2 : (g₁ * z * g₁⁻¹) * (g₁ * z * g₁⁻¹) = 1 := by
    calc (g₁ * z * g₁⁻¹) * (g₁ * z * g₁⁻¹) = g₁ * (z * z) * g₁⁻¹ := by group
      _ = 1 := by rw [hz2]; group
  have ht₁conj : IsConj z (g₁ * z * g₁⁻¹) := isConj_iff.mpr ⟨g₁, rfl⟩
  have ht₁ne : g₁ * z * g₁⁻¹ ≠ z := by
    intro htz
    apply hyne
    rw [← hzc]
    have : g₁ * z = z * g₁ := by
      calc g₁ * z = (g₁ * z * g₁⁻¹) * g₁ := by group
        _ = z * g₁ := by rw [htz]
    simp only [zc]
    calc g₁⁻¹ * z * g₁ = g₁⁻¹ * (z * g₁) := by group
      _ = g₁⁻¹ * (g₁ * z) := by rw [this]
      _ = z := by group
  have hidx := hpsp4.index
  have htsw₁ := exists_swap_of_mem_S hpair hK hSC hidx hyS (hswap) h12b ht₁S ht₁conj ht₁ne ht₁2
  obtain ⟨ht₁C', htsw₁'⟩ := htsw₁
  have hgood := concl20_14_of_good hK hz2 hcoat hsimple hyC₁ hsw₁ ht₁C htsw₁' (by
    intro f hf
    rw [hzc]
    exact h12c _ hyS hyconj ⟨q, L₁, L₂, hpair, hswap⟩ f hf)
  have hEq : Concl20_14 z g₁ = Concl20_14 z g := by
    unfold Concl20_14 Ey Hy Iy
    rw [hzc]
  rw [← hEq]
  exact hgood

end CFSG.GH74.GLS.Stage2.Final.Thm6
