module

public import Mathlib.GroupTheory.IsPerfect
public import Mathlib.GroupTheory.SpecificGroups.Alternating.Simple

public section

namespace CFSG.EvenSporadicStandard.TwoFi22.DS81.Fi24Branch

open Subgroup

open scoped Pointwise

variable {B : Type} [Group B] [Finite B]

theorem perfect_centralizes_of_card_le_four {Yb U : Subgroup B} (hY : ⁅Yb, Yb⁆ = Yb)
    (hn : ∀ y ∈ Yb, ∀ u ∈ U, y * u * y⁻¹ ∈ U) (hc : Nat.card ↥U ≤ 4) :
    ∀ y ∈ Yb, ∀ u ∈ U, y * u = u * y := by
  classical
  let conjy : ↥Yb → Equiv.Perm ↥U := fun y =>
    { toFun := fun u => ⟨(y : B) * (u : B) * (y : B)⁻¹, hn y y.2 u u.2⟩
      invFun := fun u => ⟨(y : B)⁻¹ * (u : B) * (y : B), by
        simpa using hn (y⁻¹) (Yb.inv_mem y.2) u u.2⟩
      left_inv := fun u => Subtype.ext (by group)
      right_inv := fun u => Subtype.ext (by group) }
  have conjy_apply : ∀ (y : ↥Yb) (u : ↥U),
      (conjy y) u = ⟨(y : B) * (u : B) * (y : B)⁻¹, hn y y.2 u u.2⟩ :=
    fun y u => rfl
  let ρ : ↥Yb →* Equiv.Perm ↥U :=
  { toFun := conjy
    map_one' := by
      apply Equiv.ext
      intro u
      rw [conjy_apply]
      apply Subtype.ext
      simp
    map_mul' := fun a b => by
      apply Equiv.ext
      intro u
      simp only [conjy_apply, Equiv.Perm.mul_apply, Subgroup.coe_mul, Subtype.coe_mk]
      group }
  haveI hperfY : Group.IsPerfect ↥Yb := Subgroup.isPerfect_iff.mpr hY
  haveI hperfR : Group.IsPerfect ↥ρ.range := Group.IsPerfect.range ρ
  haveI hsol : Group.IsSolvable (Equiv.Perm ↥U) := Equiv.Perm.isSolvable hc
  haveI hsub : Subsingleton ↥ρ.range := by
    rw [← not_nontrivial_iff_subsingleton]
    intro hnt
    haveI : Nontrivial ↥ρ.range := hnt
    exact (Group.IsPerfect.not_isSolvable ↥ρ.range) (inferInstance : Group.IsSolvable ↥ρ.range)
  intro y hy u hu
  have hy1 : ρ ⟨y, hy⟩ = 1 := by
    have hmem : (⟨ρ ⟨y, hy⟩, MonoidHom.mem_range.mpr ⟨⟨y, hy⟩, rfl⟩⟩ : ↥ρ.range) = 1 :=
      Subsingleton.elim _ _
    exact Subtype.ext_iff.mp hmem
  have hρapply : ((ρ ⟨y, hy⟩) ⟨u, hu⟩ : B) = y * u * y⁻¹ := by
    change ((conjy ⟨y, hy⟩) ⟨u, hu⟩ : B) = y * u * y⁻¹
    rw [conjy_apply]
  have hconj : y * u * y⁻¹ = u := by
    have h := congrArg (fun f : Equiv.Perm ↥U => ((f ⟨u, hu⟩ : ↥U) : B)) hy1
    rw [hρapply] at h
    simpa using h
  calc y * u = (y * u * y⁻¹) * y := by group
    _ = u * y := by rw [hconj]

theorem perfect_centralizes_of_centralizes_commutators {Yb W : Subgroup B} (hY : ⁅Yb, Yb⁆ = Yb)
    (hW : ∀ a ∈ W, ∀ b ∈ W, a * b = b * a) (hn : ∀ y ∈ Yb, ∀ w ∈ W, y * w * y⁻¹ ∈ W)
    (hD : ∀ y ∈ Yb, ∀ y' ∈ Yb, ∀ w ∈ W,
      y * (y' * w * y'⁻¹ * w⁻¹) = (y' * w * y'⁻¹ * w⁻¹) * y) :
    ∀ y ∈ Yb, ∀ w ∈ W, y * w = w * y := by
  haveI hperfY : Group.IsPerfect ↥Yb := Subgroup.isPerfect_iff.mpr hY
  haveI hWcomm : IsMulCommutative ↥W :=
    IsMulCommutative.of_comm (fun a b => Subtype.ext (hW a a.2 b b.2))
  intro y hy w hw
  let f : ↥Yb →* ↥W :=
  { toFun := fun a =>
      ⟨(a : B) * w * (a : B)⁻¹ * w⁻¹, W.mul_mem (hn a a.2 w hw) (W.inv_mem hw)⟩
    map_one' := by ext; simp
    map_mul' := by
      intro a b
      ext
      simp only [Subtype.coe_mk, Subgroup.coe_mul]
      have hD' : (a : B) * ((b : B) * w * (b : B)⁻¹ * w⁻¹)
          = ((b : B) * w * (b : B)⁻¹ * w⁻¹) * (a : B) := hD a a.2 b b.2 w hw
      have hW' : ((b : B) * w * (b : B)⁻¹ * w⁻¹) * ((a : B) * w * (a : B)⁻¹ * w⁻¹)
          = ((a : B) * w * (a : B)⁻¹ * w⁻¹) * ((b : B) * w * (b : B)⁻¹ * w⁻¹) :=
        hW _ (W.mul_mem (hn b b.2 w hw) (W.inv_mem hw)) _
          (W.mul_mem (hn a a.2 w hw) (W.inv_mem hw))
      calc (a : B) * (b : B) * w * ((a : B) * (b : B))⁻¹ * w⁻¹
          = (a : B) * ((b : B) * w * (b : B)⁻¹ * w⁻¹) * (a : B)⁻¹
              * ((a : B) * w * (a : B)⁻¹ * w⁻¹) := by group
        _ = ((b : B) * w * (b : B)⁻¹ * w⁻¹)
              * ((a : B) * w * (a : B)⁻¹ * w⁻¹) := by
              rw [hD']; group
        _ = ((a : B) * w * (a : B)⁻¹ * w⁻¹)
              * ((b : B) * w * (b : B)⁻¹ * w⁻¹) := hW' }
  have htop : (⊤ : Subgroup ↥Yb) ≤ f.ker := by
    rw [← Group.IsPerfect.commutator_eq_top (G := ↥Yb)]
    exact Abelianization.commutator_subset_ker f
  have hker : f.ker = ⊤ := eq_top_iff.mpr htop
  have hf1 : f ⟨y, hy⟩ = 1 := by
    have : ⟨y, hy⟩ ∈ f.ker := by rw [hker]; trivial
    simpa [MonoidHom.mem_ker] using this
  have hcomm : y * w * y⁻¹ * w⁻¹ = 1 := by
    have := congrArg (fun z : ↥W => (z : B)) hf1
    simpa [f] using this
  calc y * w = (y * w * y⁻¹) * y := by group
    _ = w * y := by
      have hyw : y * w * y⁻¹ = w := by
        have h := congrArg (fun z : B => z * w) hcomm
        simpa [mul_assoc] using h
      rw [hyw]

theorem centralizes_of_card_le_of_lattice {Yb Rb Ob Vb : Subgroup B} (hY : ⁅Yb, Yb⁆ = Yb)
    (hRc : ∀ a ∈ Rb, ∀ b ∈ Rb, a * b = b * a) (hYn : ∀ y ∈ Yb, ∀ r ∈ Rb, y * r * y⁻¹ ∈ Rb)
    (hOR : Ob ≤ Rb) (hVO : Vb ≤ Ob) (hVcard : Nat.card ↥Vb = 2)
    (hVn : ∀ y ∈ Yb, ∀ v ∈ Vb, y * v * y⁻¹ ∈ Vb)
    (hcomm : ∀ y ∈ Yb, ∀ r ∈ Rb, y * r * y⁻¹ * r⁻¹ ∈ Ob)
    (hlat : ∀ U : Subgroup B, Vb ≤ U → U ≤ Ob → (∀ y ∈ Yb, ∀ u ∈ U, y * u * y⁻¹ ∈ U) →
      Nat.card ↥U = 2 ∨ Nat.card ↥U = 2 ^ 2 ∨ Nat.card ↥U = 2 ^ 10 ∨ Nat.card ↥U = 2 ^ 11)
    {M : Subgroup B} (hM : M ≤ Rb) (hMn : ∀ y ∈ Yb, ∀ m ∈ M, y * m * y⁻¹ ∈ M)
    (hMc : Nat.card ↥M ≤ 2 ^ 7) :
    ∀ y ∈ Yb, ∀ m ∈ M, y * m = m * y := by
  haveI hperfY : Group.IsPerfect ↥Yb := Subgroup.isPerfect_iff.mpr hY
  have hDOb : ⁅Yb, M⁆ ≤ Ob := by
    rw [Subgroup.commutator_le]
    intro y hy m hm
    exact hcomm y hy m (hM hm)
  have hDM : ⁅Yb, M⁆ ≤ M := by
    rw [Subgroup.commutator_le]
    intro y hy m hm
    rw [commutatorElement_def]
    exact M.mul_mem (hMn y hy m hm) (M.inv_mem hm)
  have hYnormY : Yb ≤ Subgroup.normalizer (Yb : Set B) :=
    Subgroup.le_normalizer_iff.mpr
      (fun h hh k hk => Yb.mul_mem (Yb.mul_mem hh hk) (Yb.inv_mem hh))
  have hMnorm : Yb ≤ Subgroup.normalizer (M : Set B) := Subgroup.le_normalizer_iff.mpr hMn
  have hDmap : ∀ y' ∈ Yb, (⁅Yb, M⁆).map (MulAut.conj y') = ⁅Yb, M⁆ := by
    intro y' hy'
    rw [Subgroup.map_commutator (H₁ := Yb) (H₂ := M) (MulAut.conj y' : B →* B),
      Subgroup.mem_normalizer_iff_map_conj_eq.mp (hYnormY hy'),
      Subgroup.mem_normalizer_iff_map_conj_eq.mp (hMnorm hy')]
  have hVmap : ∀ y' ∈ Yb, Vb.map (MulAut.conj y') = Vb := fun y' hy' =>
    Subgroup.mem_normalizer_iff_map_conj_eq.mp (Subgroup.le_normalizer_iff.mpr hVn hy')
  have hUn : ∀ y' ∈ Yb, ∀ u ∈ (⁅Yb, M⁆ ⊔ Vb), y' * u * y'⁻¹ ∈ (⁅Yb, M⁆ ⊔ Vb) := by
    intro y' hy' u hu
    have hsup : (⁅Yb, M⁆ ⊔ Vb).map (MulAut.conj y') = ⁅Yb, M⁆ ⊔ Vb := by
      rw [Subgroup.map_sup (⁅Yb, M⁆) Vb (MulAut.conj y' : B →* B), hDmap y' hy', hVmap y' hy']
    have h : y' * u * y'⁻¹ ∈ (⁅Yb, M⁆ ⊔ Vb).map (MulAut.conj y') := by
      rw [Subgroup.mem_map]
      exact ⟨u, hu, by simp [MulAut.conj_apply]⟩
    rwa [hsup] at h
  have hcardD : Nat.card ↥⁅Yb, M⁆ ≤ 2 ^ 7 := (Subgroup.card_le_of_le hDM).trans hMc
  have hDleNormalizerV : ⁅Yb, M⁆ ≤ Subgroup.normalizer (Vb : Set B) := by
    rw [Subgroup.le_normalizer_iff]
    intro d hd v hv
    have hdR : d ∈ Rb := hOR (hDOb hd)
    have hvR : v ∈ Rb := hOR (hVO hv)
    rw [hRc d hdR v hvR]
    simpa [mul_assoc] using hv
  have hcoe : (↑(⁅Yb, M⁆ ⊔ Vb) : Set B) =
      ((⁅Yb, M⁆ : Subgroup B) : Set B) * (Vb : Set B) :=
    Subgroup.coe_mul_of_left_le_normalizer_right ⁅Yb, M⁆ Vb hDleNormalizerV
  have hsurj : Function.Surjective (fun p : ↥⁅Yb, M⁆ × ↥Vb =>
      (⟨p.1 * p.2, Subgroup.mul_mem_sup p.1.2 p.2.2⟩ : ↥(⁅Yb, M⁆ ⊔ Vb))) := by
    intro u
    have hu : (u : B) ∈ ((⁅Yb, M⁆ : Subgroup B) : Set B) * (Vb : Set B) := by
      rw [← hcoe]; exact u.2
    obtain ⟨d, hd, v, hv, hdv⟩ := hu
    exact ⟨(⟨d, hd⟩, ⟨v, hv⟩), Subtype.ext hdv⟩
  have hcardU : Nat.card ↥(⁅Yb, M⁆ ⊔ Vb) ≤ 2 ^ 8 := by
    calc Nat.card ↥(⁅Yb, M⁆ ⊔ Vb)
        ≤ Nat.card (↥⁅Yb, M⁆ × ↥Vb) := Nat.card_le_card_of_surjective _ hsurj
      _ = Nat.card ↥⁅Yb, M⁆ * Nat.card ↥Vb := Nat.card_prod _ _
      _ ≤ 2 ^ 7 * 2 := Nat.mul_le_mul hcardD (le_of_eq hVcard)
      _ = 2 ^ 8 := by norm_num
  have hcardUle4 : Nat.card ↥(⁅Yb, M⁆ ⊔ Vb) ≤ 4 := by
    have h := hlat (⁅Yb, M⁆ ⊔ Vb) le_sup_right (sup_le hDOb hVO) hUn
    have h8 : Nat.card ↥(⁅Yb, M⁆ ⊔ Vb) ≤ 2 ^ 8 := hcardU
    norm_num at h8
    rcases h with h | h | h | h
    · omega
    · omega
    · norm_num at h; omega
    · norm_num at h; omega
  have hcentU : ∀ y ∈ Yb, ∀ u ∈ (⁅Yb, M⁆ ⊔ Vb), y * u = u * y :=
    perfect_centralizes_of_card_le_four hY hUn hcardUle4
  have hMcomm : ∀ a ∈ M, ∀ b ∈ M, a * b = b * a :=
    fun a ha b hb => hRc a (hM ha) b (hM hb)
  refine perfect_centralizes_of_centralizes_commutators hY hMcomm hMn ?_
  intro y hy y' hy' w hw
  have hcD : y' * w * y'⁻¹ * w⁻¹ ∈ ⁅Yb, M⁆ :=
    Subgroup.commutator_mem_commutator hy' hw
  exact hcentU y hy _ (Subgroup.mem_sup_left hcD)

theorem not_centralizes_of_lattice {Yb Rb Ob Vb : Subgroup B} (hOR : Ob ≤ Rb)
    (hOc : ∀ a ∈ Ob, ∀ b ∈ Ob, a * b = b * a) (hOcard : Nat.card ↥Ob = 2 ^ 11)
    (hVO : Vb ≤ Ob) (hVcard : Nat.card ↥Vb = 2)
    (hlat : ∀ U : Subgroup B, Vb ≤ U → U ≤ Ob → (∀ y ∈ Yb, ∀ u ∈ U, y * u * y⁻¹ ∈ U) →
      Nat.card ↥U = 2 ∨ Nat.card ↥U = 2 ^ 2 ∨ Nat.card ↥U = 2 ^ 10 ∨ Nat.card ↥U = 2 ^ 11) :
    ¬ ∀ y ∈ Yb, ∀ r ∈ Rb, y * r = r * y := by
  intro hcent
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hdvd : 2 ^ 5 ∣ Nat.card ↥Ob := by
    rw [hOcard]
    exact ⟨2 ^ 6, by norm_num⟩
  have hVsub_card : Nat.card ↥(Vb.subgroupOf Ob) = 2 ^ 1 := by
    have h := Subgroup.card_subtype Ob (Vb.subgroupOf Ob)
    rw [Subgroup.subgroupOf_map_subtype, inf_eq_left.mpr hVO, hVcard] at h
    simpa using h.symm
  obtain ⟨K, hKcard, hVK⟩ := Sylow.exists_subgroup_card_pow_prime_le (G := ↥Ob) 2
    (n := 1) (m := 5) hdvd (Vb.subgroupOf Ob) hVsub_card (by norm_num)
  let U : Subgroup B := K.map Ob.subtype
  have hUcard : Nat.card ↥U = 2 ^ 5 := by
    dsimp [U]
    rw [Subgroup.card_subtype Ob K]
    exact hKcard
  have hUO : U ≤ Ob := Subgroup.map_subtype_le K
  have hVU : Vb ≤ U := by
    intro v hv
    dsimp [U]
    exact Subgroup.mem_map_of_mem (K := K) Ob.subtype
      (hVK (show (⟨v, hVO hv⟩ : ↥Ob) ∈ Vb.subgroupOf Ob from by
        rw [Subgroup.mem_subgroupOf]; exact hv))
  have hUn : ∀ y ∈ Yb, ∀ u ∈ U, y * u * y⁻¹ ∈ U := by
    intro y hy u hu
    have huR : u ∈ Rb := hOR (hUO hu)
    have hcomm : y * u = u * y := hcent y hy u huR
    rw [hcomm]
    simpa [mul_assoc] using hu
  have hcard := hlat U hVU hUO hUn
  rw [hUcard] at hcard
  rcases hcard with h | h | h | h <;> norm_num at h

end CFSG.EvenSporadicStandard.TwoFi22.DS81.Fi24Branch
