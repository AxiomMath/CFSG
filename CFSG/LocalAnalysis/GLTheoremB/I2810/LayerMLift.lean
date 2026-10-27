module

public import CFSG.LocalAnalysis.GLTheoremB.I2810.LayerMFix

public section

open CFSG.Open CFSG.LocalAnalysis.GLTheoremB CFSG.LocalAnalysis.GLTheoremB.Prop95Iv
open scoped commutatorElement

namespace CFSG.LocalAnalysis.GLTheoremB.Prop95Iv.I2810.LayerM

section General

variable {G : Type*} [Group G]

theorem commutator_mul_central {c d x y : G} (hcx : Commute c x) (hcy : Commute c y)
    (hdx : Commute d x) (hdy : Commute d y) (hcd : Commute c d) : ⁅c * x, d * y⁆ = ⁅x, y⁆ := by
  have e1 : ⁅c * x, d * y⁆ = c * (x * d * y * x⁻¹) * c⁻¹ * (y⁻¹ * d⁻¹) := by
    simp only [commutatorElement_def]; group
  have hw : Commute c (x * d * y * x⁻¹) :=
    ((hcx.mul_right hcd).mul_right hcy).mul_right hcx.inv_right
  have e2 : c * (x * d * y * x⁻¹) * c⁻¹ = x * d * y * x⁻¹ := by
    rw [hw.eq]; group
  rw [e1, e2]
  have hw' : Commute d (y * x⁻¹ * y⁻¹) := (hdy.mul_right hdx.inv_right).mul_right hdy.inv_right
  have e3 : x * d * y * x⁻¹ * (y⁻¹ * d⁻¹) = x * (d * (y * x⁻¹ * y⁻¹) * d⁻¹) := by group
  rw [e3, hw'.eq]
  simp only [commutatorElement_def]; group

theorem conj_eq_of_perfect_central {K : Subgroup G} (hK : ⁅K, K⁆ = K) {δ : G}
    (h : ∀ x ∈ K, ∃ c ∈ K, (∀ y ∈ K, c * y = y * c) ∧ δ * x * δ⁻¹ = c * x) :
    ∀ x ∈ K, δ * x * δ⁻¹ = x := by
  have hle : ⁅K, K⁆ ≤ K ⊓ Subgroup.centralizer ({δ} : Set G) := by
    rw [Subgroup.commutator_le]
    intro x hx y hy
    refine Subgroup.mem_inf.2 ⟨hK ▸ Subgroup.commutator_mem_commutator hx hy,
      Subgroup.mem_centralizer_iff.2 ?_⟩
    intro g hg
    rw [Set.mem_singleton_iff] at hg
    subst hg
    obtain ⟨c, hcK, hcc, hcx⟩ := h x hx
    obtain ⟨d, hdK, hdd, hdy⟩ := h y hy
    have key : g * ⁅x, y⁆ * g⁻¹ = ⁅c * x, d * y⁆ := by
      have e : g * ⁅x, y⁆ * g⁻¹ = ⁅g * x * g⁻¹, g * y * g⁻¹⁆ := by
        simp only [commutatorElement_def]; group
      rw [e, hcx, hdy]
    rw [commutator_mul_central (hcc x hx) (hcc y hy) (hdd x hx) (hdd y hy) (hcc d hdK)] at key
    calc g * ⁅x, y⁆ = g * ⁅x, y⁆ * g⁻¹ * g := by group
      _ = ⁅x, y⁆ * g := by rw [key]
  intro x hx
  have hx' : x ∈ K ⊓ Subgroup.centralizer ({δ} : Set G) := hle (by rw [hK]; exact hx)
  have := (Subgroup.mem_centralizer_iff.1 (Subgroup.mem_inf.1 hx').2) δ rfl
  calc δ * x * δ⁻¹ = x * δ * δ⁻¹ := by rw [this]
    _ = x := by group

theorem commutator_closure_le_of_normalizes {K : Subgroup G} {S : Set G}
    (hN : ∀ s ∈ S, s ∈ Subgroup.normalizer (K : Set G)) (hS : ∀ s ∈ S, ∀ t ∈ S, ⁅s, t⁆ ∈ K) :
    ⁅Subgroup.closure S, Subgroup.closure S⁆ ≤ K := by
  have hclN : Subgroup.closure S ≤ Subgroup.normalizer (K : Set G) := (Subgroup.closure_le _).2 hN
  have hconj : ∀ a ∈ Subgroup.closure S, ∀ x ∈ K, a * x * a⁻¹ ∈ K := fun a ha x hx =>
    (Subgroup.mem_normalizer_iff.1 (hclN ha) x).1 hx
  have hconj' : ∀ a ∈ Subgroup.closure S, ∀ x ∈ K, a⁻¹ * x * a ∈ K := fun a ha x hx => by
    simpa using hconj a⁻¹ (Subgroup.inv_mem _ ha) x hx
  have step1 : ∀ b ∈ S, ∀ a ∈ Subgroup.closure S, ⁅a, b⁆ ∈ K := by
    intro b hb a ha
    refine Subgroup.closure_induction (p := fun a _ => ⁅a, b⁆ ∈ K) ?_ ?_ ?_ ?_ ha
    · intro x hx
      exact hS x hx b hb
    · simp
    · intro x y hx hy ihx ihy
      have e : ⁅x * y, b⁆ = x * ⁅y, b⁆ * x⁻¹ * ⁅x, b⁆ := by
        simp only [commutatorElement_def]; group
      rw [e]
      exact K.mul_mem (hconj x hx _ ihy) ihx
    · intro x hx ihx
      have e : ⁅x⁻¹, b⁆ = x⁻¹ * (⁅x, b⁆)⁻¹ * x := by
        simp only [commutatorElement_def]; group
      rw [e]
      exact hconj' x hx _ (K.inv_mem ihx)
  rw [Subgroup.commutator_le]
  intro a ha b hb
  refine Subgroup.closure_induction (p := fun b _ => ⁅a, b⁆ ∈ K) ?_ ?_ ?_ ?_ hb
  · intro x hx
    exact step1 x hx a ha
  · simp
  · intro x y hx hy ihx ihy
    have e : ⁅a, x * y⁆ = ⁅a, x⁆ * (x * ⁅a, y⁆ * x⁻¹) := by
      simp only [commutatorElement_def]; group
    rw [e]
    exact K.mul_mem ihx (hconj x hx _ ihy)
  · intro x hx ihx
    have e : ⁅a, x⁻¹⁆ = x⁻¹ * (⁅a, x⁆)⁻¹ * x := by
      simp only [commutatorElement_def]; group
    rw [e]
    exact hconj' x hx _ (K.inv_mem ihx)

end General

section ASD

variable {V : Type} [Group V] [Finite V]
variable {Kh Eh : Subgroup (MulAut V)} {n : ℕ} {π : ↥Kh →* ↥(alternatingGroup (Fin n))}
  {Vv V₄ : Subgroup ↥(alternatingGroup (Fin n))}

theorem asd_conj_mem (d : ASData Kh Eh n π Vv V₄) {ε : MulAut V} (hε : ε ∈ Eh) {x : MulAut V}
    (hx : x ∈ Kh) : ε * x * ε⁻¹ ∈ Kh :=
  (Subgroup.mem_normalizer_iff.1 (d.norm hε) x).1 hx

theorem center_coe_comm {z : ↥Kh} (hz : z ∈ Subgroup.center ↥Kh) {y : MulAut V} (hy : y ∈ Kh) :
    (z : MulAut V) * y = y * (z : MulAut V) :=
  (congrArg Subtype.val (Subgroup.mem_center_iff.1 hz ⟨y, hy⟩)).symm

def Induces (π : ↥Kh →* ↥(alternatingGroup (Fin n))) (ε : MulAut V)
    (v : ↥(alternatingGroup (Fin n))) : Prop :=
  ∀ k k' : ↥Kh, (k' : MulAut V) = ε * k * ε⁻¹ → π k' = v * π k * v⁻¹

theorem induces_unique (d : ASData Kh Eh n π Vv V₄) {ε : MulAut V} (hε : ε ∈ Eh)
    {v v' : ↥(alternatingGroup (Fin n))} (h : Induces π ε v) (h' : Induces π ε v') : v = v' := by
  have hcen : v⁻¹ * v' ∈ Subgroup.center ↥(alternatingGroup (Fin n)) := by
    rw [Subgroup.mem_center_iff]
    intro y
    obtain ⟨k, rfl⟩ := d.surj y
    have h1 := h k ⟨ε * k * ε⁻¹, asd_conj_mem d hε k.2⟩ rfl
    have h2 := h' k ⟨ε * k * ε⁻¹, asd_conj_mem d hε k.2⟩ rfl
    rw [h1] at h2
    calc π k * (v⁻¹ * v') = v⁻¹ * (v * π k * v⁻¹) * v' := by group
      _ = v⁻¹ * (v' * π k * v'⁻¹) * v' := by rw [h2]
      _ = v⁻¹ * v' * π k := by group
  have h4 : 4 ≤ Nat.card (Fin n) := by
    rw [Nat.card_eq_fintype_card, Fintype.card_fin]
    have := d.hn
    omega
  rw [alternatingGroup.center_eq_bot h4, Subgroup.mem_bot, inv_mul_eq_one] at hcen
  exact hcen

theorem induces_inj (d : ASData Kh Eh n π Vv V₄) {ε ε' : MulAut V} (hε : ε ∈ Eh) (hε' : ε' ∈ Eh)
    {v : ↥(alternatingGroup (Fin n))} (h : Induces π ε v) (h' : Induces π ε' v) : ε = ε' := by
  have hcent : ∀ x ∈ Kh, (ε'⁻¹ * ε) * x * (ε'⁻¹ * ε)⁻¹ = x := by
    apply conj_eq_of_perfect_central d.perf
    intro x hx
    let x₁ : ↥Kh := ⟨x, hx⟩
    let a : ↥Kh := ⟨ε * x * ε⁻¹, asd_conj_mem d hε hx⟩
    let b : ↥Kh := ⟨ε' * x * ε'⁻¹, asd_conj_mem d hε' hx⟩
    have h1 : π a = v * π x₁ * v⁻¹ := h x₁ a rfl
    have h2 : π b = v * π x₁ * v⁻¹ := h' x₁ b rfl
    have hz : a * b⁻¹ ∈ Subgroup.center ↥Kh := by
      rw [← d.ker, MonoidHom.mem_ker, map_mul, map_inv, h1, h2, mul_inv_cancel]
    have hab : (a : MulAut V) = ((a * b⁻¹ : ↥Kh) : MulAut V) * (b : MulAut V) := by
      rw [← Subgroup.coe_mul, inv_mul_cancel_right]
    have hzK : ((a * b⁻¹ : ↥Kh) : MulAut V) ∈ Kh := (a * b⁻¹).2
    refine ⟨ε'⁻¹ * ((a * b⁻¹ : ↥Kh) : MulAut V) * ε', ?_, ?_, ?_⟩
    · have := asd_conj_mem d (Eh.inv_mem hε') hzK
      simpa using this
    · intro y hy
      have hy' : ε' * y * ε'⁻¹ ∈ Kh := asd_conj_mem d hε' hy
      have hcomm := center_coe_comm hz hy'
      calc ε'⁻¹ * ((a * b⁻¹ : ↥Kh) : MulAut V) * ε' * y
          = ε'⁻¹ * (((a * b⁻¹ : ↥Kh) : MulAut V) * (ε' * y * ε'⁻¹)) * ε' := by group
        _ = ε'⁻¹ * ((ε' * y * ε'⁻¹) * ((a * b⁻¹ : ↥Kh) : MulAut V)) * ε' := by rw [hcomm]
        _ = y * (ε'⁻¹ * ((a * b⁻¹ : ↥Kh) : MulAut V) * ε') := by group
    · have hxe : (ε * x * ε⁻¹ : MulAut V) = ((a * b⁻¹ : ↥Kh) : MulAut V) * (ε' * x * ε'⁻¹) := hab
      calc (ε'⁻¹ * ε) * x * (ε'⁻¹ * ε)⁻¹ = ε'⁻¹ * (ε * x * ε⁻¹) * ε' := by group
        _ = ε'⁻¹ * (((a * b⁻¹ : ↥Kh) : MulAut V) * (ε' * x * ε'⁻¹)) * ε' := by rw [hxe]
        _ = (ε'⁻¹ * ((a * b⁻¹ : ↥Kh) : MulAut V) * ε') * x := by group
  have hδ : ε'⁻¹ * ε = 1 := by
    apply d.faith _ (Eh.mul_mem (Eh.inv_mem hε') hε)
    intro k hk
    have := hcent k hk
    calc ε'⁻¹ * ε * k = (ε'⁻¹ * ε * k * (ε'⁻¹ * ε)⁻¹) * (ε'⁻¹ * ε) := by group
      _ = k * (ε'⁻¹ * ε) := by rw [this]
  exact (inv_mul_eq_one.1 hδ).symm

theorem conj_eq_of_induces (d : ASData Kh Eh n π Vv V₄) {ε : MulAut V} (hε : ε ∈ Eh)
    {v : ↥(alternatingGroup (Fin n))} (h : Induces π ε v) (k : ↥Kh) (hk : π k = v) :
    ∀ x x' : ↥Kh, (x' : MulAut V) = ε * x * ε⁻¹ → x' = k * x * k⁻¹ := by
  have hcent : ∀ x ∈ Kh, ((k : MulAut V)⁻¹ * ε) * x * ((k : MulAut V)⁻¹ * ε)⁻¹ = x := by
    apply conj_eq_of_perfect_central d.perf
    intro x hx
    let x₁ : ↥Kh := ⟨x, hx⟩
    let a : ↥Kh := ⟨ε * x * ε⁻¹, asd_conj_mem d hε hx⟩
    have h1 : π a = π k * π x₁ * (π k)⁻¹ := by rw [hk]; exact h x₁ a rfl
    have hz : (k * x₁ * k⁻¹)⁻¹ * a ∈ Subgroup.center ↥Kh := by
      rw [← d.ker, MonoidHom.mem_ker, map_mul, map_inv, map_mul, map_mul, map_inv, h1]
      group
    have hzK : (((k * x₁ * k⁻¹)⁻¹ * a : ↥Kh) : MulAut V) ∈ Kh := ((k * x₁ * k⁻¹)⁻¹ * a).2
    have hka : (a : MulAut V) = (k : MulAut V) * x * (k : MulAut V)⁻¹ *
        (((k * x₁ * k⁻¹)⁻¹ * a : ↥Kh) : MulAut V) := by
      have : a = (k * x₁ * k⁻¹) * ((k * x₁ * k⁻¹)⁻¹ * a) := by group
      exact congrArg Subtype.val this
    refine ⟨(((k * x₁ * k⁻¹)⁻¹ * a : ↥Kh) : MulAut V), hzK, fun y hy => center_coe_comm hz hy, ?_⟩
    have hzk := center_coe_comm hz k.2
    have hzx := center_coe_comm hz hx
    calc ((k : MulAut V)⁻¹ * ε) * x * ((k : MulAut V)⁻¹ * ε)⁻¹
        = (k : MulAut V)⁻¹ * (ε * x * ε⁻¹) * k := by group
      _ = (k : MulAut V)⁻¹ * ((k : MulAut V) * x * (k : MulAut V)⁻¹ *
            (((k * x₁ * k⁻¹)⁻¹ * a : ↥Kh) : MulAut V)) * k := by
          rw [show (ε * x * ε⁻¹ : MulAut V) = (a : MulAut V) from rfl, ← hka]
      _ = x * ((k : MulAut V)⁻¹ * (((k * x₁ * k⁻¹)⁻¹ * a : ↥Kh) : MulAut V) * k) := by group
      _ = x * (((k * x₁ * k⁻¹)⁻¹ * a : ↥Kh) : MulAut V) := by
          rw [show (k : MulAut V)⁻¹ * (((k * x₁ * k⁻¹)⁻¹ * a : ↥Kh) : MulAut V) * k =
            (((k * x₁ * k⁻¹)⁻¹ * a : ↥Kh) : MulAut V) by
              rw [mul_assoc, hzk, inv_mul_cancel_left]]
      _ = (((k * x₁ * k⁻¹)⁻¹ * a : ↥Kh) : MulAut V) * x := hzx.symm
  intro x x' hx'
  apply Subtype.ext
  have h1 := hcent x x.2
  rw [hx']
  rw [Subgroup.coe_mul, Subgroup.coe_mul, Subgroup.coe_inv]
  calc ε * (x : MulAut V) * ε⁻¹ = (k : MulAut V) * ((k : MulAut V)⁻¹ * ε * x * (ε⁻¹ * k)) *
        (k : MulAut V)⁻¹ := by group
    _ = (k : MulAut V) * x * (k : MulAut V)⁻¹ := by
        rw [show (k : MulAut V)⁻¹ * ε * x * (ε⁻¹ * k) =
          ((k : MulAut V)⁻¹ * ε) * x * ((k : MulAut V)⁻¹ * ε)⁻¹ by group, h1]

theorem card_Vv_eq_aux (d : ASData Kh Eh n π Vv V₄) : Nat.card ↥Vv = Nat.card ↥Eh := by
  classical
  have h1 : ∀ ε : ↥Eh, ∃ v : ↥Vv, Induces π (ε : MulAut V) (v : ↥(alternatingGroup (Fin n))) :=
    fun ε => by
      obtain ⟨v, hv, h⟩ := d.act₁ ε ε.2
      exact ⟨⟨v, hv⟩, h⟩
  choose f hf using h1
  have hinj : Function.Injective f := by
    intro ε ε' he
    have h' : Induces π (ε' : MulAut V) (f ε : ↥(alternatingGroup (Fin n))) := by
      rw [he]; exact hf ε'
    exact Subtype.ext (induces_inj d ε.2 ε'.2 (hf ε) h')
  have hsurj : Function.Surjective f := by
    intro v
    obtain ⟨ε, hε, h⟩ := d.act₂ v v.2
    refine ⟨⟨ε, hε⟩, Subtype.ext ?_⟩
    exact induces_unique d hε (hf ⟨ε, hε⟩) h
  exact (Nat.card_congr (Equiv.ofBijective f ⟨hinj, hsurj⟩)).symm

theorem lift_decomp_aux (d : ASData Kh Eh n π Vv V₄) :
    (∀ ε ∈ Eh, ∃ k : ↥Kh, π k ∈ Vv ∧
      ∀ x x' : ↥Kh, (x' : MulAut V) = ε * x * ε⁻¹ → x' = k * x * k⁻¹) ∧
    (∀ v ∈ Vv, ∃ ε ∈ Eh, ∃ k : ↥Kh, π k = v ∧
      ∀ x x' : ↥Kh, (x' : MulAut V) = ε * x * ε⁻¹ → x' = k * x * k⁻¹) := by
  refine ⟨fun ε hε => ?_, fun v hv => ?_⟩
  · obtain ⟨v, hv, h⟩ := d.act₁ ε hε
    obtain ⟨k, hk⟩ := d.surj v
    exact ⟨k, by rw [hk]; exact hv, conj_eq_of_induces d hε h k hk⟩
  · obtain ⟨ε, hε, h⟩ := d.act₂ v hv
    obtain ⟨k, hk⟩ := d.surj v
    exact ⟨ε, hε, k, hk, conj_eq_of_induces d hε h k hk⟩

end ASD

section Core

variable {V : Type} [Group V] [Finite V]
variable {Kh Eh : Subgroup (MulAut V)} {n : ℕ} {π : ↥Kh →* ↥(alternatingGroup (Fin n))}
  {Vv V₄ : Subgroup ↥(alternatingGroup (Fin n))}

@[expose] noncomputable def Phi (Kh : Subgroup (MulAut V)) :
    ↥Kh × ↥(Subgroup.centralizer (Kh : Set (MulAut V))) →* MulAut V :=
  MonoidHom.noncommCoprod Kh.subtype (Subgroup.centralizer (Kh : Set (MulAut V))).subtype
    (fun k c => (Subgroup.mem_centralizer_iff.1 c.2 k k.2))

theorem Phi_apply (k : ↥Kh) (c : ↥(Subgroup.centralizer (Kh : Set (MulAut V)))) :
    Phi Kh (k, c) = (k : MulAut V) * (c : MulAut V) := rfl

theorem centralizes_of_rel (d : ASData Kh Eh n π Vv V₄) {ε : MulAut V} (hε : ε ∈ Eh) {k : ↥Kh}
    (hk : ∀ x x' : ↥Kh, (x' : MulAut V) = ε * x * ε⁻¹ → x' = k * x * k⁻¹) :
    (k : MulAut V)⁻¹ * ε ∈ Subgroup.centralizer (Kh : Set (MulAut V)) := by
  rw [Subgroup.mem_centralizer_iff]
  intro h hh
  have h0 := hk ⟨h, hh⟩ ⟨ε * h * ε⁻¹, asd_conj_mem d hε hh⟩ rfl
  have h1 : ε * h * ε⁻¹ = (k : MulAut V) * h * (k : MulAut V)⁻¹ := congrArg Subtype.val h0
  calc h * ((k : MulAut V)⁻¹ * ε)
      = (k : MulAut V)⁻¹ * ((k : MulAut V) * h * (k : MulAut V)⁻¹) * ε := by group
    _ = (k : MulAut V)⁻¹ * (ε * h * ε⁻¹) * ε := by rw [h1]
    _ = (k : MulAut V)⁻¹ * ε * h := by group

theorem conj_eq_Phi (d : ASData Kh Eh n π Vv V₄) {ε : MulAut V} (hε : ε ∈ Eh) (t : ↥Kh) {k : ↥Kh}
    (hk : ∀ x x' : ↥Kh, (x' : MulAut V) = ε * x * ε⁻¹ → x' = k * x * k⁻¹) :
    (t : MulAut V) * ε * (t : MulAut V)⁻¹ =
      Phi Kh (t * k * t⁻¹, ⟨(k : MulAut V)⁻¹ * ε, centralizes_of_rel d hε hk⟩) := by
  rw [Phi_apply]
  have hc := Subgroup.mem_centralizer_iff.1 (centralizes_of_rel d hε hk) t t.2
  calc (t : MulAut V) * ε * (t : MulAut V)⁻¹
      = (t : MulAut V) * (k : MulAut V) * ((k : MulAut V)⁻¹ * ε) * (t : MulAut V)⁻¹ := by group
    _ = (t : MulAut V) * (k : MulAut V) * (t : MulAut V)⁻¹ * ((t : MulAut V) *
          ((k : MulAut V)⁻¹ * ε) * (t : MulAut V)⁻¹) := by group
    _ = (t : MulAut V) * (k : MulAut V) * (t : MulAut V)⁻¹ * ((k : MulAut V)⁻¹ * ε) := by
        rw [hc]; group
    _ = _ := by simp

theorem comm_snd_mem (d : ASData Kh Eh n π Vv V₄) {ε ε' : MulAut V} (hε : ε ∈ Eh) (hε' : ε' ∈ Eh)
    {k k' : ↥Kh} {c c' : ↥(Subgroup.centralizer (Kh : Set (MulAut V)))}
    (h : Phi Kh (k, c) = ε) (h' : Phi Kh (k', c') = ε') :
    ((⁅c, c'⁆ : ↥(Subgroup.centralizer (Kh : Set (MulAut V)))) : MulAut V) ∈ Kh := by
  have hcomm : ε * ε' = ε' * ε := by
    have := d.eab.1.is_comm.comm ⟨ε, hε⟩ ⟨ε', hε'⟩
    exact congrArg Subtype.val this
  have h1 : ⁅ε, ε'⁆ = 1 := (commutatorElement_eq_one_iff_mul_comm).2 hcomm
  have h2 : ⁅ε, ε'⁆ = Phi Kh (⁅k, k'⁆, ⁅c, c'⁆) := by
    rw [← h, ← h', ← map_commutatorElement]
    congr 1
  rw [h1, Phi_apply] at h2
  have h3 : ((⁅c, c'⁆ : ↥(Subgroup.centralizer (Kh : Set (MulAut V)))) : MulAut V) =
      ((⁅k, k'⁆ : ↥Kh) : MulAut V)⁻¹ := by
    have := congrArg (fun x => ((⁅k, k'⁆ : ↥Kh) : MulAut V)⁻¹ * x) h2
    simp only [inv_mul_cancel_left, mul_one] at this
    exact this.symm
  rw [h3]
  exact Kh.inv_mem (⁅k, k'⁆ : ↥Kh).2

theorem lift_core_aux (d : ASData Kh Eh n π Vv V₄) {s : ℕ}
    (xs : Fin s → ↥(alternatingGroup (Fin n))) :
    ∃ J : Subgroup (MulAut V), (fixV' J).index ≤ Nat.card ↥Eh ^ s ∧ ⁅J, J⁆ ≤ Kh ∧
      ∀ y : ↥Kh, π y ∈
          ⁅⨆ i, Vv.map (MulAut.conj (xs i)).toMonoidHom,
            ⨆ i, Vv.map (MulAut.conj (xs i)).toMonoidHom⁆ →
        ∃ z ∈ Subgroup.center ↥Kh, (y : MulAut V) * (z : MulAut V) ∈ ⁅J, J⁆ := by
  classical
  choose t ht using fun i => d.surj (xs i)
  let g : Fin s → MulAut V := fun i => (t i : MulAut V)
  let C : Subgroup (MulAut V) := Subgroup.centralizer (Kh : Set (MulAut V))
  let J : Subgroup (MulAut V) := ⨆ i, Eh.map (MulAut.conj (g i)).toMonoidHom
  have hconjapp : ∀ i (ε : MulAut V), (MulAut.conj (g i)).toMonoidHom ε = g i * ε * (g i)⁻¹ :=
    fun i ε => rfl
  have hJrange : J ≤ (Phi Kh).range := by
    refine iSup_le fun i => ?_
    rintro _ ⟨ε, hε, rfl⟩
    obtain ⟨k, -, hk⟩ := (lift_decomp_aux d).1 ε hε
    refine ⟨(t i * k * (t i)⁻¹, ⟨(k : MulAut V)⁻¹ * ε, centralizes_of_rel d hε hk⟩), ?_⟩
    rw [← conj_eq_Phi d hε (t i) hk, hconjapp]
  have hcomm : ⁅J, J⁆ ≤ Kh := by
    have hJ : J = Subgroup.closure (⋃ i, ((Eh.map (MulAut.conj (g i)).toMonoidHom :
        Subgroup (MulAut V)) : Set (MulAut V))) := Subgroup.iSup_eq_closure _
    rw [hJ]
    apply commutator_closure_le_of_normalizes
    · intro x hx
      obtain ⟨i, hx⟩ := Set.mem_iUnion.1 hx
      obtain ⟨ε, hε, rfl⟩ := hx
      have h1 : g i ∈ Subgroup.normalizer (Kh : Set (MulAut V)) := Subgroup.le_normalizer (t i).2
      rw [hconjapp]
      exact Subgroup.mul_mem _ (Subgroup.mul_mem _ h1 (d.norm hε)) (Subgroup.inv_mem _ h1)
    · intro x hx y hy
      obtain ⟨i, hx⟩ := Set.mem_iUnion.1 hx
      obtain ⟨ε, hε, rfl⟩ := hx
      obtain ⟨j, hy⟩ := Set.mem_iUnion.1 hy
      obtain ⟨ε', hε', rfl⟩ := hy
      obtain ⟨k, -, hk⟩ := (lift_decomp_aux d).1 ε hε
      obtain ⟨k', -, hk'⟩ := (lift_decomp_aux d).1 ε' hε'
      have e1 : (MulAut.conj (g i)).toMonoidHom ε =
          Phi Kh (t i * k * (t i)⁻¹, ⟨(k : MulAut V)⁻¹ * ε, centralizes_of_rel d hε hk⟩) := by
        rw [hconjapp]; exact conj_eq_Phi d hε (t i) hk
      have e2 : (MulAut.conj (g j)).toMonoidHom ε' =
          Phi Kh (t j * k' * (t j)⁻¹, ⟨(k' : MulAut V)⁻¹ * ε', centralizes_of_rel d hε' hk'⟩) := by
        rw [hconjapp]; exact conj_eq_Phi d hε' (t j) hk'
      have hP : Phi Kh (k, ⟨(k : MulAut V)⁻¹ * ε, centralizes_of_rel d hε hk⟩) = ε := by
        rw [Phi_apply]; simp
      have hP' : Phi Kh (k', ⟨(k' : MulAut V)⁻¹ * ε', centralizes_of_rel d hε' hk'⟩) = ε' := by
        rw [Phi_apply]; simp
      have hcc := comm_snd_mem d hε hε' hP hP'
      rw [e1, e2, ← map_commutatorElement]
      have hprod : ⁅((t i * k * (t i)⁻¹ : ↥Kh),
            (⟨(k : MulAut V)⁻¹ * ε, centralizes_of_rel d hε hk⟩ : ↥C)),
          ((t j * k' * (t j)⁻¹ : ↥Kh),
            (⟨(k' : MulAut V)⁻¹ * ε', centralizes_of_rel d hε' hk'⟩ : ↥C))⁆ =
          (⁅(t i * k * (t i)⁻¹ : ↥Kh), (t j * k' * (t j)⁻¹ : ↥Kh)⁆,
            ⁅(⟨(k : MulAut V)⁻¹ * ε, centralizes_of_rel d hε hk⟩ : ↥C),
              (⟨(k' : MulAut V)⁻¹ * ε', centralizes_of_rel d hε' hk'⟩ : ↥C)⁆) :=
        Prod.ext (by simp [commutatorElement_def]) (by simp [commutatorElement_def])
      rw [hprod, Phi_apply]
      exact Kh.mul_mem (⁅(t i * k * (t i)⁻¹ : ↥Kh), (t j * k' * (t j)⁻¹ : ↥Kh)⁆).2 hcc
  refine ⟨J, (fix_index_conj_aux g Eh).trans (Nat.pow_le_pow_left d.off s), hcomm, ?_⟩
  let Jt : Subgroup (↥Kh × ↥C) := J.comap (Phi Kh)
  have hJmap : Jt.map (Phi Kh) = J := Subgroup.map_comap_eq_self hJrange
  let ψ : ↥Kh × ↥C →* ↥(alternatingGroup (Fin n)) := π.comp (MonoidHom.fst _ _)
  have hGle : (⨆ i, Vv.map (MulAut.conj (xs i)).toMonoidHom) ≤ Jt.map ψ := by
    refine iSup_le fun i => ?_
    rintro _ ⟨v, hv, rfl⟩
    obtain ⟨ε, hε, k, hkv, hk⟩ := (lift_decomp_aux d).2 v hv
    refine ⟨(t i * k * (t i)⁻¹, ⟨(k : MulAut V)⁻¹ * ε, centralizes_of_rel d hε hk⟩), ?_, ?_⟩
    · show Phi Kh _ ∈ J
      rw [← conj_eq_Phi d hε (t i) hk]
      exact Subgroup.mem_iSup_of_mem i ⟨ε, hε, rfl⟩
    · show π (t i * k * (t i)⁻¹) = _
      rw [map_mul, map_mul, map_inv, ht, hkv]
      rfl
  have hcommG : ⁅⨆ i, Vv.map (MulAut.conj (xs i)).toMonoidHom,
      ⨆ i, Vv.map (MulAut.conj (xs i)).toMonoidHom⁆ ≤ (⁅Jt, Jt⁆).map ψ := by
    rw [Subgroup.map_commutator]
    exact Subgroup.commutator_mono hGle hGle
  intro y hy
  obtain ⟨q, hq, hqy⟩ := hcommG hy
  have hΦq : Phi Kh q ∈ ⁅J, J⁆ := by
    have := Subgroup.mem_map_of_mem (Phi Kh) hq
    rwa [Subgroup.map_commutator, hJmap] at this
  have hKq : Phi Kh q ∈ Kh := hcomm hΦq
  have hq1 : (q.1 : MulAut V) * (q.2 : MulAut V) = Phi Kh q := by
    rw [← Phi_apply]
  have hq2 : (q.2 : MulAut V) ∈ Kh := by
    have : (q.2 : MulAut V) = (q.1 : MulAut V)⁻¹ * Phi Kh q := by rw [← hq1]; group
    rw [this]
    exact Kh.mul_mem (Kh.inv_mem q.1.2) hKq
  have hπq : π q.1 = π y := hqy
  refine ⟨(y⁻¹ * q.1) * ⟨(q.2 : MulAut V), hq2⟩, ?_, ?_⟩
  · refine Subgroup.mul_mem _ ?_ ?_
    · rw [← d.ker, MonoidHom.mem_ker, map_mul, map_inv, hπq, inv_mul_cancel]
    · rw [Subgroup.mem_center_iff]
      intro h
      apply Subtype.ext
      exact Subgroup.mem_centralizer_iff.1 q.2.2 h h.2
  · have hfin : (y : MulAut V) * ((y⁻¹ * q.1 * ⟨(q.2 : MulAut V), hq2⟩ : ↥Kh) : MulAut V) =
        Phi Kh q := by
      rw [← hq1]
      simp only [Subgroup.coe_mul, Subgroup.coe_inv]
      group
    rw [hfin]
    exact hΦq

theorem kh_le_J_aux (d : ASData Kh Eh n π Vv V₄) {J : Subgroup (MulAut V)}
    {G : Subgroup ↥(alternatingGroup (Fin n))} (hG : ⊤ ≤ G) (_hJK : ⁅J, J⁆ ≤ Kh)
    (hJ : ∀ y : ↥Kh, π y ∈ ⁅G, G⁆ →
      ∃ z ∈ Subgroup.center ↥Kh, (y : MulAut V) * (z : MulAut V) ∈ ⁅J, J⁆) : Kh ≤ J := by
  have h5 : 5 ≤ Nat.card (Fin n) := by
    rw [Nat.card_eq_fintype_card, Fintype.card_fin]; exact d.hn
  have hGG : ⁅G, G⁆ = ⊤ := by
    rw [eq_top_iff]
    have h1 : ⁅(⊤ : Subgroup ↥(alternatingGroup (Fin n))), ⊤⁆ = ⊤ :=
      commutator_alternatingGroup_eq_top h5
    rw [← h1]
    exact Subgroup.commutator_mono hG hG
  have hlift : ∀ x ∈ Kh, ∃ z ∈ Subgroup.center ↥Kh, x * (z : MulAut V) ∈ J := by
    intro x hx
    obtain ⟨z, hz, hxz⟩ := hJ ⟨x, hx⟩ (by rw [hGG]; trivial)
    exact ⟨z, hz, Subgroup.commutator_le_self J hxz⟩
  conv_lhs => rw [← d.perf]
  rw [Subgroup.commutator_le]
  intro x hx y hy
  obtain ⟨z₁, hz₁, hxz₁⟩ := hlift x hx
  obtain ⟨z₂, hz₂, hyz₂⟩ := hlift y hy
  have e : ⁅x, y⁆ = ⁅(z₁ : MulAut V) * x, (z₂ : MulAut V) * y⁆ := by
    have h1 : Commute (z₁ : MulAut V) x := center_coe_comm hz₁ hx
    have h2 : Commute (z₁ : MulAut V) y := center_coe_comm hz₁ hy
    have h3 : Commute (z₂ : MulAut V) x := center_coe_comm hz₂ hx
    have h4 : Commute (z₂ : MulAut V) y := center_coe_comm hz₂ hy
    have h5' : Commute (z₁ : MulAut V) (z₂ : MulAut V) := center_coe_comm hz₁ z₂.2
    exact (commutator_mul_central h1 h2 h3 h4 h5').symm
  have hxJ : (z₁ : MulAut V) * x ∈ J := by rw [center_coe_comm hz₁ hx]; exact hxz₁
  have hyJ : (z₂ : MulAut V) * y ∈ J := by rw [center_coe_comm hz₂ hy]; exact hyz₂
  rw [e, commutatorElement_def]
  exact J.mul_mem (J.mul_mem (J.mul_mem hxJ hyJ) (J.inv_mem hxJ)) (J.inv_mem hyJ)

theorem cover_A9_aux (d : ASData Kh Eh n π Vv V₄) {J : Subgroup (MulAut V)}
    {G F : Subgroup ↥(alternatingGroup (Fin n))} (hFG : F ≤ G)
    (hF : Nonempty (↥F ≃* ↥(alternatingGroup (Fin 9)))) (hJK : ⁅J, J⁆ ≤ Kh)
    (hJ : ∀ y : ↥Kh, π y ∈ ⁅G, G⁆ →
      ∃ z ∈ Subgroup.center ↥Kh, (y : MulAut V) * (z : MulAut V) ∈ ⁅J, J⁆) :
    ∃ Y : Subgroup (MulAut V), Y ≤ J ∧ ∃ π' : ↥Y →* ↥(alternatingGroup (Fin 9)),
      Function.Surjective π' ∧ π'.ker ≤ Subgroup.center ↥Y := by
  obtain ⟨e⟩ := hF
  have h9 : 5 ≤ Nat.card (Fin 9) := by simp
  have hperf9 : Group.IsPerfect (alternatingGroup (Fin 9)) :=
    ⟨commutator_alternatingGroup_eq_top h9⟩
  haveI := hperf9
  have hperfF : Group.IsPerfect ↥F :=
    Group.IsPerfect.ofSurjective (f := e.symm.toMonoidHom) e.symm.surjective
  have hFF : ⁅F, F⁆ = F := Subgroup.commutator_eq_self
  have hFGG : F ≤ ⁅G, G⁆ := by
    calc F = ⁅F, F⁆ := hFF.symm
      _ ≤ ⁅G, G⁆ := Subgroup.commutator_mono hFG hFG
  let Y : Subgroup (MulAut V) := (F.comap π).map Kh.subtype ⊓ ⁅J, J⁆
  have hYK : Y ≤ Kh := fun y hy => hJK (Subgroup.mem_inf.1 hy).2
  have hYπ : ∀ y : ↥Y, π (Subgroup.inclusion hYK y) ∈ F := by
    intro y
    obtain ⟨y', hy', hyy⟩ := (Subgroup.mem_inf.1 y.2).1
    have : y' = Subgroup.inclusion hYK y := Subtype.ext hyy
    rw [← this]
    exact hy'
  let ι : ↥Y →* ↥F := ((π.comp (Subgroup.inclusion hYK)).codRestrict F hYπ)
  have hYJ : Y ≤ J := fun y hy => Subgroup.commutator_le_self J (Subgroup.mem_inf.1 hy).2
  refine ⟨Y, hYJ, e.toMonoidHom.comp ι, ?_, ?_⟩
  · intro a
    have hf : ((e.symm a : ↥F) : ↥(alternatingGroup (Fin n))) ∈ ⁅G, G⁆ := hFGG (e.symm a).2
    obtain ⟨y₀, hy₀⟩ := d.surj (e.symm a : ↥F)
    obtain ⟨z, hz, hw⟩ := hJ y₀ (by rw [hy₀]; exact hf)
    have hzk : π z = 1 := by rw [← MonoidHom.mem_ker, d.ker]; exact hz
    have hπw : π (y₀ * z) = (e.symm a : ↥F) := by rw [map_mul, hzk, mul_one, hy₀]
    have hwY : ((y₀ * z : ↥Kh) : MulAut V) ∈ Y := by
      refine Subgroup.mem_inf.2 ⟨⟨y₀ * z, ?_, rfl⟩, ?_⟩
      · show π (y₀ * z) ∈ F
        rw [hπw]; exact (e.symm a).2
      · rw [Subgroup.coe_mul]; exact hw
    refine ⟨⟨_, hwY⟩, ?_⟩
    show e (ι ⟨_, hwY⟩) = a
    have : ι ⟨_, hwY⟩ = e.symm a := Subtype.ext hπw
    rw [this, MulEquiv.apply_symm_apply]
  · intro y hy
    have h1 : e (ι y) = 1 := hy
    have h2 : ι y = 1 := e.injective (h1.trans (map_one e).symm)
    have h3 : π (Subgroup.inclusion hYK y) = 1 := congrArg Subtype.val h2
    have hz : Subgroup.inclusion hYK y ∈ Subgroup.center ↥Kh := by
      rw [← d.ker]; exact h3
    rw [Subgroup.mem_center_iff]
    intro y'
    apply Subtype.ext
    exact (center_coe_comm hz (hYK y'.2)).symm

end Core

end CFSG.LocalAnalysis.GLTheoremB.Prop95Iv.I2810.LayerM
