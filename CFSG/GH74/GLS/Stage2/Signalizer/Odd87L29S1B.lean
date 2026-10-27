module

public import CFSG.GH74.GLS.Stage2.Signalizer.Odd87L29S1A
public import CFSG.GH74.GLS.Stage2.Signalizer.Odd87L29Pair

public section

namespace CFSG.GH74.GLS.Stage2.Signalizer.Odd87

open Subgroup CFSG CFSG.GH74.GLS CFSG.GH74.GLS.Stage2.Local CFSG.GH74.GLS.Stage1.Main

namespace L29S1

section Data

variable {H : Type} [Group H]

structure SwapData (L₁ L₂ : Subgroup H) (u : H) : Prop where
  comm : ∀ a ∈ L₁, ∀ b ∈ L₂, a * b = b * a
  card : Nat.card ↥(L₁ ⊓ L₂) = 2
  cent : ∀ c : H, (∀ a ∈ L₁, c * a = a * c) → (∀ b ∈ L₂, c * b = b * c) → c ∈ L₁ ⊓ L₂
  sq : u * u = 1
  map₁₂ : L₁.map (MulAut.conj u).toMonoidHom = L₂
  map₂₁ : L₂.map (MulAut.conj u).toMonoidHom = L₁

variable {L₁ L₂ : Subgroup H} {u : H}

theorem SwapData.mem₂ (h : SwapData L₁ L₂ u) {a : H} (ha : a ∈ L₁) : u * a * u⁻¹ ∈ L₂ := by
  rw [← h.map₁₂]
  exact Subgroup.mem_map.mpr ⟨a, ha, by simp [MulAut.conj_apply]⟩

theorem SwapData.mem₁ (h : SwapData L₁ L₂ u) {b : H} (hb : b ∈ L₂) : u * b * u⁻¹ ∈ L₁ := by
  rw [← h.map₂₁]
  exact Subgroup.mem_map.mpr ⟨b, hb, by simp [MulAut.conj_apply]⟩

theorem SwapData.exists₂ (h : SwapData L₁ L₂ u) {b : H} (hb : b ∈ L₂) :
    ∃ a ∈ L₁, u * a * u⁻¹ = b := by
  rw [← h.map₁₂] at hb
  obtain ⟨a, ha, rfl⟩ := Subgroup.mem_map.mp hb
  exact ⟨a, ha, by simp [MulAut.conj_apply]⟩

theorem SwapData.conj_conj (h : SwapData L₁ L₂ u) (x : H) : u * (u * x * u⁻¹) * u⁻¹ = x := by
  have h1 : u⁻¹ * u⁻¹ = 1 := by rw [← mul_inv_rev, h.sq, inv_one]
  calc u * (u * x * u⁻¹) * u⁻¹ = (u * u) * x * (u⁻¹ * u⁻¹) := by group
    _ = x := by rw [h.sq, h1, one_mul, mul_one]

theorem SwapData.mem_inf_conj (h : SwapData L₁ L₂ u) {x : H} (hx : x ∈ L₁ ⊓ L₂) :
    u * x * u⁻¹ ∈ L₁ ⊓ L₂ := ⟨h.mem₁ hx.2, h.mem₂ hx.1⟩

theorem SwapData.commute_u [Finite H] (h : SwapData L₁ L₂ u) {x : H} (hx : x ∈ L₁ ⊓ L₂) :
    u * x = x * u :=
  L29Pair.commute_of_mem_of_card_le_two (Z := L₁ ⊓ L₂) h.card.le hx (h.mem_inf_conj hx)

theorem SwapData.mul_self_of_mem_inf (h : SwapData L₁ L₂ u) {x : H} (hx : x ∈ L₁ ⊓ L₂) :
    x * x = 1 := by
  have h1 : (⟨x, hx⟩ : ↥(L₁ ⊓ L₂)) ^ Nat.card ↥(L₁ ⊓ L₂) = 1 := pow_card_eq_one'
  rw [h.card] at h1
  simpa [pow_two] using congrArg Subtype.val h1

theorem SwapData.centralizes₂ (h : SwapData L₁ L₂ u) {c : H} (hcu : c * u = u * c)
    (hc : ∀ b ∈ L₁, c * b = b * c) : ∀ b ∈ L₂, c * b = b * c := by
  intro b hb
  obtain ⟨a, ha, rfl⟩ := h.exists₂ hb
  have h1 : c * a * c⁻¹ = a := by rw [hc a ha]; group
  calc c * (u * a * u⁻¹) = ((c * u) * a * (c * u)⁻¹) * c := by group
    _ = (u * (c * a * c⁻¹) * u⁻¹) * c := by rw [hcu]; group
    _ = (u * a * u⁻¹) * c := by rw [h1]

theorem SwapData.mem_inf_of_centralizes (h : SwapData L₁ L₂ u) {c : H} (hcu : c * u = u * c)
    (hc : ∀ b ∈ L₁, c * b = b * c) : c ∈ L₁ ⊓ L₂ :=
  h.cent c hc (h.centralizes₂ hcu hc)

end Data

section Stab

variable {H : Type} [Group H] {L₁ L₂ : Subgroup H} {u : H}

@[expose] def stab (L₁ L₂ : Subgroup H) (u : H) : Subgroup H :=
  centralizer ({u} : Set H) ⊓ normalizer (L₁ : Set H) ⊓ normalizer (L₂ : Set H)

theorem mem_stab_iff {e : H} : e ∈ stab L₁ L₂ u ↔
    e * u = u * e ∧ e ∈ normalizer (L₁ : Set H) ∧ e ∈ normalizer (L₂ : Set H) := by
  unfold stab
  rw [Subgroup.mem_inf, Subgroup.mem_inf, Subgroup.mem_centralizer_singleton_iff, and_assoc]

theorem mem_normalizer_of_conj_mem {g : H} {L : Subgroup H} (h1 : ∀ x ∈ L, g * x * g⁻¹ ∈ L)
    (h2 : ∀ x ∈ L, g⁻¹ * x * g ∈ L) : g ∈ normalizer (L : Set H) := by
  rw [Subgroup.mem_normalizer_iff]
  intro x
  refine ⟨h1 x, fun hx => ?_⟩
  have := h2 _ hx
  simpa [mul_assoc] using this

theorem SwapData.mem_normalizer₂ (h : SwapData L₁ L₂ u) {e : H} (hcu : e * u = u * e)
    (he : e ∈ normalizer (L₁ : Set H)) : e ∈ normalizer (L₂ : Set H) := by
  have key : ∀ g : H, g * u = u * g → g ∈ normalizer (L₁ : Set H) →
      ∀ x ∈ L₂, g * x * g⁻¹ ∈ L₂ := by
    intro g hgu hg x hx
    obtain ⟨b, hb, rfl⟩ := h.exists₂ hx
    have hb' : g * b * g⁻¹ ∈ L₁ := (Subgroup.mem_normalizer_iff.mp hg b).mp hb
    have : g * (u * b * u⁻¹) * g⁻¹ = u * (g * b * g⁻¹) * u⁻¹ := by
      calc g * (u * b * u⁻¹) * g⁻¹ = (g * u) * b * (g * u)⁻¹ := by group
        _ = (u * g) * b * (u * g)⁻¹ := by rw [hgu]
        _ = u * (g * b * g⁻¹) * u⁻¹ := by group
    rw [this]
    exact h.mem₂ hb'
  refine mem_normalizer_of_conj_mem (key e hcu he) ?_
  have hu' : e⁻¹ * u = u * e⁻¹ := by
    calc e⁻¹ * u = e⁻¹ * (u * e) * e⁻¹ := by group
      _ = e⁻¹ * (e * u) * e⁻¹ := by rw [hcu]
      _ = u * e⁻¹ := by group
  intro x hx
  have := key e⁻¹ hu' ((normalizer (L₁ : Set H)).inv_mem he) x hx
  simpa using this

@[expose] def diagHom (h : SwapData L₁ L₂ u) : ↥L₁ →* H where
  toFun a := (a : H) * (u * (a : H) * u⁻¹)
  map_one' := by simp
  map_mul' a b := by
    have hc := h.comm b b.2 (u * (a : H) * u⁻¹) (h.mem₂ a.2)
    calc ((a * b : ↥L₁) : H) * (u * ((a * b : ↥L₁) : H) * u⁻¹)
        = (a : H) * ((b : H) * (u * (a : H) * u⁻¹)) * (u * (b : H) * u⁻¹) := by
          simp only [Subgroup.coe_mul]; group
      _ = (a : H) * ((u * (a : H) * u⁻¹) * (b : H)) * (u * (b : H) * u⁻¹) := by rw [hc]
      _ = ((a : H) * (u * (a : H) * u⁻¹)) * ((b : H) * (u * (b : H) * u⁻¹)) := by group

theorem diagHom_apply (h : SwapData L₁ L₂ u) (a : ↥L₁) :
    diagHom h a = (a : H) * (u * (a : H) * u⁻¹) := rfl

theorem diagHom_conj (h : SwapData L₁ L₂ u) (a : ↥L₁) {x : H} (hx : x ∈ L₁) :
    diagHom h a * x * (diagHom h a)⁻¹ = (a : H) * x * (a : H)⁻¹ := by
  rw [diagHom_apply]
  have hwL : u * (a : H) * u⁻¹ ∈ L₂ := h.mem₂ a.2
  generalize u * (a : H) * u⁻¹ = w at hwL ⊢
  have hwx : w * x = x * w := (h.comm x hx w hwL).symm
  have h1 : w * x * w⁻¹ = x := by rw [hwx]; group
  calc (a : H) * w * x * ((a : H) * w)⁻¹ = (a : H) * (w * x * w⁻¹) * (a : H)⁻¹ := by group
    _ = (a : H) * x * (a : H)⁻¹ := by rw [h1]

theorem diagHom_inv_conj (h : SwapData L₁ L₂ u) (a : ↥L₁) {x : H} (hx : x ∈ L₁) :
    (diagHom h a)⁻¹ * x * diagHom h a = (a : H)⁻¹ * x * (a : H) := by
  have := diagHom_conj h a⁻¹ hx
  simpa only [map_inv, inv_inv, Subgroup.coe_inv] using this

theorem diagHom_mul_u (h : SwapData L₁ L₂ u) (a : ↥L₁) :
    diagHom h a * u = u * diagHom h a := by
  have h1 : u * diagHom h a * u⁻¹ = diagHom h a := by
    rw [diagHom_apply]
    calc u * ((a : H) * (u * (a : H) * u⁻¹)) * u⁻¹
        = (u * (a : H) * u⁻¹) * (u * (u * (a : H) * u⁻¹) * u⁻¹) := by group
      _ = (u * (a : H) * u⁻¹) * (a : H) := by rw [h.conj_conj]
      _ = (a : H) * (u * (a : H) * u⁻¹) := (h.comm a a.2 _ (h.mem₂ a.2)).symm
  exact (mul_inv_eq_iff_eq_mul.mp h1).symm

theorem diagHom_mem_normalizer₁ (h : SwapData L₁ L₂ u) (a : ↥L₁) :
    diagHom h a ∈ normalizer (L₁ : Set H) := by
  refine mem_normalizer_of_conj_mem (fun x hx => ?_) (fun x hx => ?_)
  · rw [diagHom_conj h a hx]
    exact L₁.mul_mem (L₁.mul_mem a.2 hx) (L₁.inv_mem a.2)
  · rw [diagHom_inv_conj h a hx]
    exact L₁.mul_mem (L₁.mul_mem (L₁.inv_mem a.2) hx) a.2

theorem diagHom_mem_stab (h : SwapData L₁ L₂ u) (a : ↥L₁) : diagHom h a ∈ stab L₁ L₂ u :=
  mem_stab_iff.mpr ⟨diagHom_mul_u h a, diagHom_mem_normalizer₁ h a,
    h.mem_normalizer₂ (diagHom_mul_u h a) (diagHom_mem_normalizer₁ h a)⟩

theorem conj_diagHom (h : SwapData L₁ L₂ u) {e : H} (he : e ∈ stab L₁ L₂ u) (a : ↥L₁) :
    e * diagHom h a * e⁻¹ = diagHom h ⟨e * (a : H) * e⁻¹,
      (Subgroup.mem_normalizer_iff.mp (mem_stab_iff.mp he).2.1 a).mp a.2⟩ := by
  obtain ⟨heu, -, -⟩ := mem_stab_iff.mp he
  rw [diagHom_apply, diagHom_apply]
  show e * ((a : H) * (u * (a : H) * u⁻¹)) * e⁻¹ =
    (e * (a : H) * e⁻¹) * (u * (e * (a : H) * e⁻¹) * u⁻¹)
  calc e * ((a : H) * (u * (a : H) * u⁻¹)) * e⁻¹
      = (e * (a : H) * e⁻¹) * ((e * u) * (a : H) * (e * u)⁻¹) := by group
    _ = (e * (a : H) * e⁻¹) * ((u * e) * (a : H) * (u * e)⁻¹) := by rw [heu]
    _ = (e * (a : H) * e⁻¹) * (u * (e * (a : H) * e⁻¹) * u⁻¹) := by group

theorem normal_diag_subgroupOf (h : SwapData L₁ L₂ u) :
    ((diagHom h).range.subgroupOf (stab L₁ L₂ u)).Normal := by
  refine ⟨fun n hn g => ?_⟩
  rw [Subgroup.mem_subgroupOf] at hn ⊢
  obtain ⟨a, ha⟩ := hn
  have h1 : ((g * n * g⁻¹ : ↥(stab L₁ L₂ u)) : H) = (g : H) * (n : H) * (g : H)⁻¹ := rfl
  rw [h1, ← ha, conj_diagHom h g.2 a]
  exact ⟨_, rfl⟩

@[expose] def stabAct (L₁ L₂ : Subgroup H) (u : H) : ↥(stab L₁ L₂ u) →* MulAut ↥L₁ :=
  actOnKHom L₁ (stab L₁ L₂ u) (fun _ he => (mem_stab_iff.mp he).2.1)

theorem stabAct_apply (e : ↥(stab L₁ L₂ u)) (b : ↥L₁) :
    ((stabAct L₁ L₂ u e b : ↥L₁) : H) = (e : H) * (b : H) * (e : H)⁻¹ := rfl

theorem stabAct_diagHom (h : SwapData L₁ L₂ u) (a : ↥L₁) :
    stabAct L₁ L₂ u ⟨diagHom h a, diagHom_mem_stab h a⟩ = MulAut.conj a := by
  ext b
  rw [stabAct_apply]
  simp only [MulAut.conj_apply, Subgroup.coe_mul, Subgroup.coe_inv]
  exact diagHom_conj h a b.2

end Stab

section Main

variable {H : Type} [Group H] [Finite H] {L₁ L₂ : Subgroup H} {u : H}

theorem mem_diagHom_range_of_two_power (h : SwapData L₁ L₂ u)
    (hout : ∀ α β : MulAut ↥L₁, α * β * α⁻¹ * β⁻¹ ∈ (MulAut.conj : ↥L₁ →* MulAut ↥L₁).range)
    {y : H} (hy : y ∈ O2Of (stab L₁ L₂ u)) {k : ℕ} (hyk : y ^ 2 ^ k = 1) :
    y ∈ (diagHom h).range := by
  set I : Subgroup (MulAut ↥L₁) := (MulAut.conj : ↥L₁ →* MulAut ↥L₁).range with hI
  have hIn : I.Normal := by
    refine ⟨fun n hn g => ?_⟩
    obtain ⟨q, rfl⟩ := hn
    exact ⟨g q, by ext x; simp [MulAut.conj_apply]⟩
  have hA : ∀ x y : MulAut ↥L₁ ⧸ I, x * y = y * x := by
    intro x y
    induction x using QuotientGroup.induction_on with | H α => ?_
    induction y using QuotientGroup.induction_on with | H β => ?_
    rw [← QuotientGroup.mk_mul, ← QuotientGroup.mk_mul, QuotientGroup.eq]
    have := hout β⁻¹ α⁻¹
    simpa [mul_assoc] using this
  let ψ : ↥(stab L₁ L₂ u) →* MulAut ↥L₁ ⧸ I := (QuotientGroup.mk' I).comp (stabAct L₁ L₂ u)
  let Δ' : Subgroup ↥(stab L₁ L₂ u) := (diagHom h).range.subgroupOf (stab L₁ L₂ u)
  have : Δ'.Normal := normal_diag_subgroupOf h
  let Z : Subgroup ↥(stab L₁ L₂ u) := (L₁ ⊓ L₂).subgroupOf (stab L₁ L₂ u)
  have hΔ : Δ' ≤ ψ.ker := by
    intro x hx
    obtain ⟨a, ha⟩ := Subgroup.mem_subgroupOf.mp hx
    rw [MonoidHom.mem_ker]
    show QuotientGroup.mk' I (stabAct L₁ L₂ u x) = 1
    have hx' : x = ⟨diagHom h a, diagHom_mem_stab h a⟩ := Subtype.ext ha.symm
    rw [hx', stabAct_diagHom h a]
    exact (QuotientGroup.eq_one_iff _).mpr ⟨a, rfl⟩
  have hZc : Z ≤ center ↥(stab L₁ L₂ u) := by
    intro z hz
    rw [Subgroup.mem_center_iff]
    intro e
    have hz' : (z : H) ∈ L₁ ⊓ L₂ := hz
    obtain ⟨-, he1, he2⟩ := mem_stab_iff.mp e.2
    have h1 : (e : H) * z * (e : H)⁻¹ ∈ L₁ ⊓ L₂ :=
      ⟨(Subgroup.mem_normalizer_iff.mp he1 z).mp hz'.1,
        (Subgroup.mem_normalizer_iff.mp he2 z).mp hz'.2⟩
    exact Subtype.ext (L29Pair.commute_of_mem_of_card_le_two (Z := L₁ ⊓ L₂) h.card.le hz' h1)
  have hZ : IsPGroup 2 ↥Z := by
    intro z
    refine ⟨1, Subtype.ext (Subtype.ext ?_)⟩
    have := h.mul_self_of_mem_inf (show (((z : ↥(stab L₁ L₂ u)) : H)) ∈ L₁ ⊓ L₂ from z.2)
    simpa [pow_two] using this
  have hker : ∀ e : ↥(stab L₁ L₂ u), ψ e = 1 → ∃ d ∈ Δ', ∃ z ∈ Z, e = d * z := by
    intro e he
    obtain ⟨a, ha⟩ := (QuotientGroup.eq_one_iff _).mp he
    have hconj : ∀ b ∈ L₁, (e : H) * b * (e : H)⁻¹ = (a : H) * b * (a : H)⁻¹ := by
      intro b hb
      have := congrArg (fun α : MulAut ↥L₁ => ((α ⟨b, hb⟩ : ↥L₁) : H)) ha
      simpa [MulAut.conj_apply, stabAct_apply] using this.symm
    let d : ↥(stab L₁ L₂ u) := ⟨diagHom h a, diagHom_mem_stab h a⟩
    refine ⟨d, Subgroup.mem_subgroupOf.mpr ⟨a, rfl⟩, d⁻¹ * e, ?_, by group⟩
    show (((d⁻¹ * e : ↥(stab L₁ L₂ u)) : H)) ∈ L₁ ⊓ L₂
    have hcoe : (((d⁻¹ * e : ↥(stab L₁ L₂ u)) : H)) = (diagHom h a)⁻¹ * (e : H) := rfl
    obtain ⟨heu, -, -⟩ := mem_stab_iff.mp e.2
    have hdu := diagHom_mul_u h a
    have hcu : (diagHom h a)⁻¹ * (e : H) * u = u * ((diagHom h a)⁻¹ * (e : H)) :=
      ((Commute.inv_left (hdu : Commute (diagHom h a) u)).mul_left (heu : Commute (e : H) u))
    rw [hcoe]
    refine h.mem_inf_of_centralizes hcu (fun b hb => ?_)
    have h1 : (diagHom h a)⁻¹ * (e : H) * b * ((diagHom h a)⁻¹ * (e : H))⁻¹ = b := by
      calc (diagHom h a)⁻¹ * (e : H) * b * ((diagHom h a)⁻¹ * (e : H))⁻¹
          = (diagHom h a)⁻¹ * ((e : H) * b * (e : H)⁻¹) * diagHom h a := by group
        _ = (diagHom h a)⁻¹ * ((a : H) * b * (a : H)⁻¹) * diagHom h a := by rw [hconj b hb]
        _ = (a : H)⁻¹ * ((a : H) * b * (a : H)⁻¹) * (a : H) :=
            diagHom_inv_conj h a (L₁.mul_mem (L₁.mul_mem a.2 hb) (L₁.inv_mem a.2))
        _ = b := by group
    exact mul_inv_eq_iff_eq_mul.mp h1
  obtain ⟨x, hx, rfl⟩ := Subgroup.mem_map.mp hy
  have hxk : x ^ 2 ^ k = 1 := Subtype.ext (by simpa using hyk)
  exact Subgroup.mem_subgroupOf.mp
    (mem_of_two_power_of_mem_oResidual hA ψ Δ' Z hΔ hZc hZ hker hx hxk)

end Main

end L29S1

end CFSG.GH74.GLS.Stage2.Signalizer.Odd87
