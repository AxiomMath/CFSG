module

public import CFSG.LocalAnalysis.SectionRank.PRank
public import CFSG.Assembly.Defs
public import CFSG.LocalAnalysis.GLTheoremB.Defs

public section

namespace CFSG.HardMathSupport.Solomon.UniquenessMaximal

open CFSG.Open CFSG.LocalAnalysis.GLTheoremB

variable {A : Type*} [Group A]

@[expose] def Centerless (W : Subgroup A) : Prop := ∀ x ∈ W, (∀ y ∈ W, x * y = y * x) → x = 1

theorem Centerless.of_center_eq_bot {W : Subgroup A} (h : Subgroup.center ↥W = ⊥) : Centerless W := by
  intro x hx hc
  have : (⟨x, hx⟩ : ↥W) ∈ Subgroup.center ↥W := by
    rw [Subgroup.mem_center_iff]
    intro y
    exact Subtype.ext (hc y y.2).symm
  rw [h, Subgroup.mem_bot] at this
  exact congrArg Subtype.val this

theorem card_inf_normalizer_le [Finite A] {p : ℕ} {W₀ B' : Subgroup A}
    (hB'el : IsElemAbelian p B') (hcl : Centerless W₀)
    (hinner : ∀ φ : MulAut ↥W₀, φ ^ p = 1 → ∃ w : ↥W₀, φ = MulAut.conj w) {w : ℕ}
    (hw : ∀ E : Subgroup A, E ≤ W₀ → IsElemAbelian p E → Nat.card E ≤ p ^ w) :
    Nat.card (B' ⊓ Subgroup.normalizer (W₀ : Set A) : Subgroup A) ≤
      Nat.card (B' ⊓ Subgroup.centralizer (W₀ : Set A) : Subgroup A) * p ^ w := by
  set N₀ := Subgroup.normalizer (W₀ : Set A) with hN₀
  set B₀ : Subgroup A := B' ⊓ N₀ with hB₀
  set B₁ : Subgroup A := B' ⊓ Subgroup.centralizer (W₀ : Set A) with hB₁
  have hB₀N : B₀ ≤ N₀ := inf_le_right
  have hB₁B₀ : B₁ ≤ B₀ := inf_le_inf_left _ (Subgroup.centralizer_le_normalizer _)
  let ψ₀ : ↥B₀ →* MulAut ↥W₀ := W₀.normalizerMonoidHom.comp (Subgroup.inclusion hB₀N)
  have hker : ψ₀.ker = B₁.subgroupOf B₀ := by
    ext b
    have h1 : ψ₀ b = 1 ↔ (Subgroup.inclusion hB₀N b) ∈ W₀.normalizerMonoidHom.ker := by
      rw [MonoidHom.mem_ker]; rfl
    rw [MonoidHom.mem_ker, h1, Subgroup.normalizerMonoidHom_ker, Subgroup.mem_subgroupOf,
      Subgroup.mem_subgroupOf]
    constructor
    · intro h
      exact ⟨b.2.1, h⟩
    · intro h
      exact h.2
  have hcardker : Nat.card ψ₀.ker = Nat.card B₁ := by
    rw [hker]
    exact Nat.card_congr (Subgroup.subgroupOfEquivOfLe hB₁B₀).toEquiv
  have hmul := Subgroup.card_ker_mul_card_range ψ₀
  rw [hcardker] at hmul
  rw [← hmul]
  refine Nat.mul_le_mul_left _ ?_
  set R : Subgroup (MulAut ↥W₀) := ψ₀.range with hR
  let c : ↥W₀ →* MulAut ↥W₀ := MulAut.conj
  have hcinj : Function.Injective c := by
    rw [← MonoidHom.ker_eq_bot_iff, eq_bot_iff]
    intro x hx
    rw [MonoidHom.mem_ker] at hx
    apply Subgroup.mem_bot.2
    apply Subtype.ext
    apply hcl x.1 x.2
    intro y hy
    have := congrArg (fun φ : MulAut ↥W₀ => (φ ⟨y, hy⟩ : A)) hx
    simp only [MulAut.one_apply] at this
    have h2 : (x : A) * y * (x : A)⁻¹ = y := by simpa [c, MulAut.conj_apply] using this
    rw [mul_inv_eq_iff_eq_mul] at h2
    exact h2
  have hBcomm : ∀ a b : B₀, a * b = b * a := by
    intro a b
    have := hB'el.1
    have h := mul_comm' (⟨a, a.2.1⟩ : B') ⟨b, b.2.1⟩
    apply Subtype.ext
    exact congrArg (fun x : ↥B' => (x : A)) h
  have hBpow : ∀ a : B₀, a ^ p = 1 := fun a => Subtype.ext (hB'el.2 a a.2.1)
  have hRle : R ≤ c.range := by
    rintro _ ⟨b, rfl⟩
    have hp1 : ψ₀ b ^ p = 1 := by rw [← map_pow, hBpow, map_one]
    obtain ⟨w, hw'⟩ := hinner _ hp1
    exact ⟨w, hw'.symm⟩
  set R' : Subgroup ↥W₀ := R.comap c with hR'
  have hR'map : R'.map c = R := Subgroup.map_comap_eq_self hRle
  have hR'card : Nat.card R' = Nat.card R := by
    rw [← hR'map]
    exact (Subgroup.card_map_of_injective hcinj).symm
  have hR'el : IsElemAbelian p R' := by
    refine ⟨⟨⟨fun a b => ?_⟩⟩, fun x hx => ?_⟩
    · apply Subtype.ext
      apply hcinj
      rw [Subgroup.coe_mul, Subgroup.coe_mul, map_mul, map_mul]
      obtain ⟨x, hx⟩ := a.2
      obtain ⟨y, hy⟩ := b.2
      rw [← hx, ← hy, ← map_mul, ← map_mul, hBcomm]
    · apply hcinj
      obtain ⟨y, hy⟩ := hx
      rw [map_pow, map_one, ← hy, ← map_pow, hBpow, map_one]
  have hM := CFSG.SectionRank.isElemAbelian_map hR'el W₀.subtype
  have hMle : R'.map W₀.subtype ≤ W₀ := Subgroup.map_subtype_le _
  have := hw _ hMle hM
  rwa [Subgroup.card_map_of_injective W₀.subtype_injective, hR'card] at this

section Family

variable {ι : Type*} [Fintype ι] {V : ι → Subgroup A}

theorem eq_one_of_mem_iSup_of_centralizes
    (hcomm : Pairwise fun i j => ∀ x y : A, x ∈ V i → y ∈ V j → Commute x y) (hind : iSupIndep V)
    (hcl : ∀ i, Centerless (V i)) {z : A} (hz : z ∈ ⨆ i, V i)
    (hzc : ∀ i, ∀ w ∈ V i, z * w = w * z) : z = 1 := by
  classical
  let ψ := Subgroup.noncommPiCoprod (H := V) hcomm
  have hinj : Function.Injective ψ := Subgroup.injective_noncommPiCoprod_of_iSupIndep hind
  have hrange : ψ.range = ⨆ i, V i := Subgroup.noncommPiCoprod_range
  rw [← hrange] at hz
  obtain ⟨u, rfl⟩ := hz
  have hu : ∀ i, (u i : A) = 1 := by
    intro i
    apply hcl i (u i) (u i).2
    intro w hw
    have h1 := hzc i w hw
    have h2 : ψ (Pi.mulSingle i (⟨w, hw⟩ : V i)) = w := Subgroup.noncommPiCoprod_mulSingle _ _
    rw [← h2] at h1
    have h3 : u * Pi.mulSingle i (⟨w, hw⟩ : V i) = Pi.mulSingle i (⟨w, hw⟩ : V i) * u := by
      apply hinj
      rw [map_mul, map_mul]
      exact h1
    have h4 := congrFun h3 i
    simp only [Pi.mul_apply, Pi.mulSingle_eq_same] at h4
    exact congrArg Subtype.val h4
  have : u = 1 := by
    funext i
    exact Subtype.ext (hu i)
  rw [this, map_one]

theorem exists_elemAbelian_pi {p w : ℕ} {E : ι → Subgroup A} (hEV : ∀ i, E i ≤ V i)
    (hcomm : Pairwise fun i j => ∀ x y : A, x ∈ V i → y ∈ V j → Commute x y)
    (hind : iSupIndep V) (hEel : ∀ i, IsElemAbelian p (E i))
    (hEcard : ∀ i, Nat.card (E i) = p ^ w) :
    ∃ S : Subgroup A, IsElemAbelian p S ∧ S ≤ ⨆ i, V i ∧
      Nat.card S = p ^ (w * Fintype.card ι) := by
  classical
  have hcommE : Pairwise fun i j => ∀ x y : A, x ∈ E i → y ∈ E j → Commute x y :=
    fun i j hij x y hx hy => hcomm hij x y (hEV i hx) (hEV j hy)
  have hindE : iSupIndep E := hind.mono hEV
  let ψ := Subgroup.noncommPiCoprod (H := E) hcommE
  have hinj : Function.Injective ψ := Subgroup.injective_noncommPiCoprod_of_iSupIndep hindE
  have hrange : ψ.range = ⨆ i, E i := Subgroup.noncommPiCoprod_range
  have hdcomm : ∀ u v : (∀ i, E i), u * v = v * u := by
    intro u v
    funext i
    have := (hEel i).1
    exact mul_comm' (u i) (v i)
  have hdpow : ∀ u : (∀ i, E i), u ^ p = 1 := by
    intro u
    funext i
    exact Subtype.ext ((hEel i).2 (u i) (u i).2)
  refine ⟨ψ.range, ⟨⟨⟨fun a b => ?_⟩⟩, fun y hy => ?_⟩, ?_, ?_⟩
  · obtain ⟨u, hu⟩ := a.2
    obtain ⟨v, hv⟩ := b.2
    apply Subtype.ext
    change (a : A) * b = b * a
    rw [← hu, ← hv, ← map_mul, ← map_mul, hdcomm]
  · obtain ⟨u, rfl⟩ := hy
    rw [← map_pow, hdpow, map_one]
  · rw [hrange]
    exact iSup_mono hEV
  · rw [← Nat.card_congr (MonoidHom.ofInjective hinj).toEquiv, Nat.card_pi]
    simp only [hEcard, Finset.prod_const, Finset.card_univ]
    rw [← pow_mul, mul_comm]

end Family

end CFSG.HardMathSupport.Solomon.UniquenessMaximal
