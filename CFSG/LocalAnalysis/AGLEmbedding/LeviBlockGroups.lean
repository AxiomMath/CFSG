module

import CFSG.LocalAnalysis.AGLEmbedding.BlockParabThreeLeviCover
public import CFSG.Assembly.Subnormal

public section

namespace CFSG.AGLEmbedding.LeviBlock

section Factor

variable {V W Q : Type*} [Group V] [Group W] [Group Q]

theorem exists_factor (f : V →* W) (hf : Function.Surjective f) (ψ : V →* Q)
    (hψ : Function.Surjective ψ) (hk : f.ker ≤ ψ.ker) :
    ∃ ψ' : W →* Q, Function.Surjective ψ' ∧ ψ'.ker ≤ ψ.ker.map f := by
  refine ⟨f.liftOfSurjective hf ⟨ψ, hk⟩, ?_, ?_⟩
  · intro y
    obtain ⟨x, rfl⟩ := hψ y
    exact ⟨f x, by simp⟩
  · intro w hw
    obtain ⟨x, rfl⟩ := hf w
    refine ⟨x, MonoidHom.mem_ker.mpr ?_, rfl⟩
    rw [MonoidHom.mem_ker] at hw
    simpa using hw

theorem le_ker_of_isPGroup_two [Finite Q] [IsSimpleGroup Q] (h3 : 3 ∣ Nat.card Q)
    (ψ : V →* Q) (hψ : Function.Surjective ψ) {K : Subgroup V} [hK : K.Normal]
    (hK2 : IsPGroup 2 K) : K ≤ ψ.ker := by
  have := hK.map ψ hψ
  rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal (K.map ψ) with h | h
  · exact (Subgroup.map_eq_bot_iff K).mp h
  · exfalso
    have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
    have h2 : IsPGroup 2 (⊤ : Subgroup Q) := h ▸ hK2.map ψ
    obtain ⟨n, hn⟩ := IsPGroup.iff_card.mp h2
    rw [Subgroup.card_top] at hn
    rw [hn] at h3
    exact absurd (Nat.Prime.dvd_of_dvd_pow Nat.prime_three h3) (by norm_num)

end Factor

theorem not_isPGroup_two_of_simple {T : Type} [Group T] [Finite T] [IsSimpleGroup T]
    (hT : ∃ a b : T, a * b ≠ b * a) : ¬ IsPGroup 2 T := by
  intro h2
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hlt := h2.bot_lt_center
  rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal (Subgroup.center T) with h | h
  · exact absurd h hlt.ne'
  · obtain ⟨a, b, hab⟩ := hT
    exact hab (Subgroup.mem_center_iff.mp (h ▸ Subgroup.mem_top b) a)

theorem card_center_eq_card_inf_centralizer {Y : Type*} [Group Y] (K : Subgroup Y) :
    Nat.card (Subgroup.center ↥K) =
      Nat.card (K ⊓ Subgroup.centralizer (K : Set Y) : Subgroup Y) := by
  have h : (Subgroup.center ↥K).map K.subtype = K ⊓ Subgroup.centralizer (K : Set Y) := by
    ext y
    constructor
    · rintro ⟨z, hz, rfl⟩
      refine ⟨z.2, Subgroup.mem_centralizer_iff.mpr fun k hk => ?_⟩
      exact congrArg Subtype.val (Subgroup.mem_center_iff.mp hz ⟨k, hk⟩)
    · rintro ⟨hyK, hyC⟩
      refine ⟨⟨y, hyK⟩, Subgroup.mem_center_iff.mpr fun k => Subtype.ext ?_, rfl⟩
      exact Subgroup.mem_centralizer_iff.mp hyC k k.2
  rw [← h, Subgroup.card_map_of_injective K.subtype_injective]

theorem map_center_mulEquiv {A B : Type*} [Group A] [Group B] (e : A ≃* B) :
    (Subgroup.center A).map e.toMonoidHom = Subgroup.center B := by
  ext b
  constructor
  · rintro ⟨a, ha, rfl⟩
    rw [SetLike.mem_coe, Subgroup.mem_center_iff] at ha
    rw [Subgroup.mem_center_iff]
    intro y
    obtain ⟨x, rfl⟩ := e.surjective y
    change e x * e a = e a * e x
    rw [← map_mul, ← map_mul, ha x]
  · intro hb
    refine ⟨e.symm b, ?_, by simp⟩
    rw [Subgroup.mem_center_iff] at hb
    rw [SetLike.mem_coe, Subgroup.mem_center_iff]
    intro y
    apply e.injective
    rw [map_mul, map_mul, MulEquiv.apply_symm_apply, hb (e y)]

theorem isQuasisimple_of_mulEquiv {A B : Type} [Group A] [Group B] (e : A ≃* B)
    (h : CFSG.Open.IsQuasisimple A) : CFSG.Open.IsQuasisimple B :=
  h.of_mulEquiv e.symm

theorem exists_noncomm_centerQuotient {A : Type} [Group A] (h : CFSG.Open.IsQuasisimple A) :
    ∃ a b : A ⧸ Subgroup.center A, a * b ≠ b * a := by
  have hZ := CFSG.AGLEmbedding.center_centerQuotient_eq_bot h
  have : IsSimpleGroup (A ⧸ Subgroup.center A) := h.2
  by_contra hc
  push Not at hc
  have htop : Subgroup.center (A ⧸ Subgroup.center A) = ⊤ := by
    rw [eq_top_iff]
    intro x _
    exact Subgroup.mem_center_iff.mpr fun y => hc y x
  rw [hZ] at htop
  obtain ⟨a, b, hab⟩ := (IsSimpleGroup.toNontrivial (G := A ⧸ Subgroup.center A)).exists_pair_ne
  have ha : a ∈ (⊥ : Subgroup _) := htop ▸ Subgroup.mem_top a
  have hb : b ∈ (⊥ : Subgroup _) := htop ▸ Subgroup.mem_top b
  rw [Subgroup.mem_bot] at ha hb
  exact hab (ha.trans hb.symm)

theorem card_mul_dvd_of_commute {Z : Type*} [Group Z] [Finite Z] (A₁ A₂ A₃ : Subgroup Z)
    (h12 : ∀ a ∈ A₁, ∀ b ∈ A₂, a * b = b * a) (h13 : ∀ a ∈ A₁, ∀ c ∈ A₃, a * c = c * a)
    (h23 : ∀ b ∈ A₂, ∀ c ∈ A₃, b * c = c * b) (hz1 : Subgroup.center ↥A₁ = ⊥)
    (hz2 : Subgroup.center ↥A₂ = ⊥) :
    Nat.card A₁ * Nat.card A₂ * Nat.card A₃ ∣ Nat.card Z := by
  let m : ↥A₁ × ↥A₂ × ↥A₃ →* Z :=
    { toFun := fun x => (x.1 : Z) * (x.2.1 : Z) * (x.2.2 : Z)
      map_one' := by simp
      map_mul' := fun x y => by
        simp only [Prod.fst_mul, Prod.snd_mul, Subgroup.coe_mul]
        have e1 := h12 _ y.1.2 _ x.2.1.2
        have e2 := h13 _ y.1.2 _ x.2.2.2
        have e3 := h23 _ y.2.1.2 _ x.2.2.2
        calc (x.1 : Z) * y.1 * (x.2.1 * y.2.1) * (x.2.2 * y.2.2)
            = x.1 * (y.1 * x.2.1) * y.2.1 * x.2.2 * y.2.2 := by group
          _ = x.1 * (x.2.1 * y.1) * y.2.1 * x.2.2 * y.2.2 := by rw [e1]
          _ = x.1 * x.2.1 * y.1 * (y.2.1 * x.2.2) * y.2.2 := by group
          _ = x.1 * x.2.1 * y.1 * (x.2.2 * y.2.1) * y.2.2 := by rw [e3]
          _ = x.1 * x.2.1 * (y.1 * x.2.2) * y.2.1 * y.2.2 := by group
          _ = x.1 * x.2.1 * (x.2.2 * y.1) * y.2.1 * y.2.2 := by rw [e2]
          _ = x.1 * x.2.1 * x.2.2 * (y.1 * y.2.1 * y.2.2) := by group }
  have hinj : Function.Injective m := by
    rw [← MonoidHom.ker_eq_bot_iff, eq_bot_iff]
    rintro ⟨a, b, c⟩ hx
    have hx' : (a : Z) * b * c = 1 := hx
    have ha : a ∈ Subgroup.center ↥A₁ := by
      rw [Subgroup.mem_center_iff]
      intro y
      have hai : (a : Z) = ((b : Z) * c)⁻¹ := by
        rw [eq_inv_iff_mul_eq_one, ← mul_assoc]; exact hx'
      have hyb : Commute (y : Z) b := h12 _ y.2 _ b.2
      have hyc : Commute (y : Z) c := h13 _ y.2 _ c.2
      have hya : Commute (y : Z) a := hai ▸ (hyb.mul_right hyc).inv_right
      exact Subtype.ext hya.eq
    rw [hz1, Subgroup.mem_bot] at ha
    subst ha
    have hx'' : (b : Z) * c = 1 := by simpa using hx'
    have hb : b ∈ Subgroup.center ↥A₂ := by
      rw [Subgroup.mem_center_iff]
      intro y
      have hbi : (b : Z) = (c : Z)⁻¹ := eq_inv_of_mul_eq_one_left hx''
      have hyc : Commute (y : Z) c := h23 _ y.2 _ c.2
      have hyb : Commute (y : Z) b := hbi ▸ hyc.inv_right
      exact Subtype.ext hyb.eq
    rw [hz2, Subgroup.mem_bot] at hb
    subst hb
    have hc : c = 1 := Subtype.ext (by simpa using hx'')
    subst hc
    rfl
  have := Subgroup.card_dvd_of_injective m hinj
  rwa [Nat.card_prod, Nat.card_prod, ← mul_assoc] at this

theorem isSolvable_pi {κ : Type} [Fintype κ] {H : κ → Type} [∀ j, Group (H j)]
    (hH : ∀ j, Group.IsSolvable (H j)) : Group.IsSolvable (∀ j, H j) := by
  classical
  choose n hn using fun j => (hH j).solvable
  refine ⟨Finset.univ.sup n, ?_⟩
  rw [eq_bot_iff]
  intro x hx
  rw [Subgroup.mem_bot]
  funext j
  have hle : derivedSeries (H j) (Finset.univ.sup n) ≤ derivedSeries (H j) (n j) :=
    derivedSeries_antitone (H j) (Finset.le_sup (Finset.mem_univ j))
  have hmap := map_derivedSeries_le_derivedSeries (Pi.evalMonoidHom H j) (Finset.univ.sup n)
  have hxj : (Pi.evalMonoidHom H j) x ∈ derivedSeries (H j) (n j) :=
    hle (hmap ⟨x, hx, rfl⟩)
  rw [hn j, Subgroup.mem_bot] at hxj
  exact hxj

end CFSG.AGLEmbedding.LeviBlock
