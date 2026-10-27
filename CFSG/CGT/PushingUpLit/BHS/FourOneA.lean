module

public import CFSG.CGT.PushingUpLit.BHS.FourDefs
public import CFSG.CGT.PushingUpLit.BHS.GlaubThmOne
public import CFSG.Quasithin.Background.B19Basic
public import CFSG.Quasithin.Background.D2Offenders

public section

local macro "comm_group" : tactic =>
  `(tactic| (apply Additive.ofMul.injective
             simp only [ofMul_mul, ofMul_inv, ofMul_div, ofMul_one]
             abel))

namespace CFSG.CGT.PushingUpLit.BHS

open CFSG.Quasithin CFSG.Quasithin.A1b CFSG.RankThree.PartOne
open scoped Pointwise

namespace FourOneTools

section Module

variable {V : Type} [CommGroup V]

theorem commute_of_commV_le {X Y : Subgroup (MulAut V)} (h₁ : commV X ≤ fixV Y)
    (h₂ : commV Y ≤ fixV X) : ∀ x ∈ X, ∀ y ∈ Y, x * y = y * x := by
  intro x hx y hy
  ext v
  have e₁ : y (x v * v⁻¹) = x v * v⁻¹ := h₁ (G6.mem_commV_of_mem hx v) y hy
  have e₂ : x (y v * v⁻¹) = y v * v⁻¹ := h₂ (G6.mem_commV_of_mem hy v) x hx
  have e₃ : x (y v) = y v * v⁻¹ * x v := by
    have h := map_mul x (y v * v⁻¹) v
    rw [e₂, inv_mul_cancel_right] at h
    exact h
  have e₄ : y (x v) = x v * v⁻¹ * y v := by
    have h := map_mul y (x v * v⁻¹) v
    rw [e₁, inv_mul_cancel_right] at h
    exact h
  simp only [MulAut.mul_apply]
  rw [e₃, e₄]
  comm_group

theorem comm_of_isQuadratic {X : Subgroup (MulAut V)} (h : IsQuadratic X) :
    ∀ x ∈ X, ∀ y ∈ X, x * y = y * x :=
  commute_of_commV_le h h

theorem apply_mem_fixV_of_comm {a : MulAut V} {B : Subgroup (MulAut V)}
    (hc : ∀ b ∈ B, a * b = b * a) {c : V} (hcB : c ∈ fixV B) : a c ∈ fixV B := by
  intro b hb
  have h := congrArg (fun g : MulAut V => g c) (hc b hb)
  simp only [MulAut.mul_apply] at h
  rw [← h, hcB b hb]

theorem commV_le_fixV_of_sup_eq_top {X Y : Subgroup (MulAut V)}
    (hc : ∀ x ∈ X, ∀ y ∈ Y, x * y = y * x) (hsup : fixV X ⊔ fixV Y = ⊤) :
    commV X ≤ fixV Y := by
  refine G6.commV_le_iff.2 fun x hx v => ?_
  have hv : v ∈ fixV X ⊔ fixV Y := by rw [hsup]; exact Subgroup.mem_top v
  obtain ⟨p, hp, q, hq, rfl⟩ := Subgroup.mem_sup.1 hv
  have h1 : x (p * q) * (p * q)⁻¹ = x q * q⁻¹ := by
    rw [map_mul, hp x hx]
    comm_group
  rw [h1]
  exact (fixV Y).mul_mem (apply_mem_fixV_of_comm (fun y hy => hc x hx y hy) hq)
    ((fixV Y).inv_mem hq)

theorem le_fixV_sSup {W : Subgroup V} {F : Set (Subgroup (MulAut V))}
    (h : ∀ B ∈ F, W ≤ fixV B) : W ≤ fixV (sSup F) := by
  intro w hw
  rw [mem_fixV_iff_le]
  exact sSup_le fun B hB => mem_fixV_iff_le.1 (h B hB hw)

end Module

section GroupTools

variable {Γ : Type*} [Group Γ]

theorem card_sup_le_mul_of_le_normalizer [Finite Γ] {H K : Subgroup Γ}
    (h : H ≤ Subgroup.normalizer (K : Set Γ)) :
    Nat.card ↥(H ⊔ K) ≤ Nat.card H * Nat.card K := by
  have hmul := Subgroup.coe_mul_of_left_le_normalizer_right H K h
  let f : H × K → ↥(H ⊔ K) := fun p => ⟨(p.1 : Γ) * p.2,
    Subgroup.mul_mem _ (Subgroup.mem_sup_left p.1.2) (Subgroup.mem_sup_right p.2.2)⟩
  have hf : Function.Surjective f := by
    rintro ⟨z, hz⟩
    have hz' : z ∈ (H : Set Γ) * (K : Set Γ) := by
      rw [← hmul]
      exact hz
    obtain ⟨x, hx, y, hy, rfl⟩ := hz'
    exact ⟨(⟨x, hx⟩, ⟨y, hy⟩), rfl⟩
  have := Nat.card_le_card_of_surjective f hf
  rwa [Nat.card_prod] at this

theorem card_lt_of_le_of_ne [Finite Γ] {H K : Subgroup Γ} (hle : H ≤ K) (hne : H ≠ K) :
    Nat.card H < Nat.card K :=
  lt_of_le_of_ne (Subgroup.card_le_of_le hle)
    fun h => hne (Subgroup.eq_of_le_of_card_ge hle h.ge)

theorem exists_normal_lt_of_isPGroup [Finite Γ] {L H : Subgroup Γ} (hL : IsPGroup 2 L)
    (hHL : H ≤ L) (hne : H ≠ L) :
    ∃ M : Subgroup Γ, H ≤ M ∧ M ≤ L ∧ M ≠ L ∧ ∀ g ∈ L, ∀ x ∈ M, g * x * g⁻¹ ∈ M := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have : Group.IsNilpotent L := hL.isNilpotent
  have hH' : H.subgroupOf L ≠ ⊤ := by
    intro h
    refine hne (le_antisymm hHL fun x hx => ?_)
    have : (⟨x, hx⟩ : L) ∈ H.subgroupOf L := by rw [h]; exact Subgroup.mem_top _
    exact this
  obtain ⟨M', hM', hHM'⟩ :=
    (IsCoatomic.eq_top_or_exists_le_coatom (H.subgroupOf L)).resolve_left hH'
  have hlt : M' < Subgroup.normalizer (M' : Set L) :=
    Group.normalizerCondition_of_isNilpotent M' (lt_top_iff_ne_top.2 hM'.ne_top)
  have hnorm : M'.Normal := Subgroup.normalizer_eq_top_iff.1 (hM'.2 _ hlt)
  refine ⟨M'.map L.subtype, fun x hx => ⟨⟨x, hHL hx⟩, hHM' hx, rfl⟩, ?_, ?_, ?_⟩
  · rintro _ ⟨y, -, rfl⟩
    exact y.2
  · intro heq
    apply hM'.ne_top
    rw [eq_top_iff]
    intro y _
    have hy : (y : Γ) ∈ M'.map L.subtype := by rw [heq]; exact y.2
    obtain ⟨z, hz, hzy⟩ := hy
    have : z = y := Subtype.ext hzy
    rwa [← this]
  · rintro g hg _ ⟨y, hy, rfl⟩
    exact ⟨⟨g, hg⟩ * y * ⟨g, hg⟩⁻¹, hnorm.conj_mem y hy _, rfl⟩

theorem comm_of_mem_sSup {F : Set (Subgroup Γ)}
    (hc : ∀ A ∈ F, ∀ B ∈ F, ∀ x ∈ A, ∀ y ∈ B, x * y = y * x) :
    ∀ x ∈ sSup F, ∀ y ∈ sSup F, x * y = y * x := by
  have h1 : ∀ B ∈ F, ∀ y ∈ B, sSup F ≤ Subgroup.centralizer {y} := by
    intro B hB y hy
    refine sSup_le fun A hA x hx => ?_
    rw [Subgroup.mem_centralizer_iff]
    intro z hz
    rw [Set.mem_singleton_iff.1 hz]
    exact hc B hB A hA y hy x hx
  intro x hx y hy
  have h2 : sSup F ≤ Subgroup.centralizer {x} := by
    refine sSup_le fun B hB w hw => ?_
    rw [Subgroup.mem_centralizer_iff]
    intro z hz
    rw [Set.mem_singleton_iff.1 hz]
    exact ((Subgroup.mem_centralizer_iff.1 (h1 B hB w hw hx)) w (Set.mem_singleton w)).symm
  exact (Subgroup.mem_centralizer_iff.1 (h2 hy)) x (Set.mem_singleton x)

theorem sq_eq_one_of_mem_sSup {F : Set (Subgroup Γ)}
    (hc : ∀ x ∈ sSup F, ∀ y ∈ sSup F, x * y = y * x) (hs : ∀ A ∈ F, ∀ x ∈ A, x ^ 2 = 1) :
    ∀ x ∈ sSup F, x ^ 2 = 1 := by
  let K : Subgroup Γ :=
    { carrier := {x | x ∈ sSup F ∧ x ^ 2 = 1}
      one_mem' := ⟨(sSup F).one_mem, one_pow 2⟩
      mul_mem' := fun {x y} hx hy => ⟨(sSup F).mul_mem hx.1 hy.1, by
        rw [Commute.mul_pow (hc x hx.1 y hy.1) 2, hx.2, hy.2, one_mul]⟩
      inv_mem' := fun {x} hx => ⟨(sSup F).inv_mem hx.1, by rw [inv_pow, hx.2, inv_one]⟩ }
  have hle : sSup F ≤ K := sSup_le fun A hA x hx => ⟨le_sSup hA hx, hs A hA x hx⟩
  exact fun x hx => (hle hx).2

theorem conjSub_eq_of_comm {g : Γ} {H : Subgroup Γ} (h : ∀ x ∈ H, g * x = x * g) :
    conjSub g H = H := by
  ext z
  rw [mem_conjSub_iff]
  constructor
  · intro hz
    have e : z * g = (g⁻¹ * z * g) * g := by rw [← h _ hz]; group
    rwa [← mul_right_cancel e] at hz
  · intro hz
    have e : g⁻¹ * z * g = z := by
      have := h z hz
      calc g⁻¹ * z * g = g⁻¹ * (z * g) := by rw [mul_assoc]
        _ = z := by rw [← this]; group
    rwa [e]

theorem mem_normalizer_of_conjSub_eq {g : Γ} {H : Subgroup Γ} (h : conjSub g H = H) :
    g ∈ Subgroup.normalizer (H : Set Γ) := by
  rw [Subgroup.mem_normalizer_iff]
  intro x
  constructor
  · intro hx
    have := mem_conjSub_of_mem (g := g) hx
    rwa [h] at this
  · intro hx
    have h1 : g * x * g⁻¹ ∈ conjSub g H := by rw [h]; exact hx
    rw [mem_conjSub_iff] at h1
    simpa [mul_assoc] using h1

end GroupTools

end FourOneTools

end CFSG.CGT.PushingUpLit.BHS
