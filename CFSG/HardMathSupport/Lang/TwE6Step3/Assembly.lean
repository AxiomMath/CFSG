module

public import CFSG.HardMathSupport.Lang.TwE6Step3.Basic
public import CFSG.HardMathSupport.Lang.SeitzPlane.TwistedE6Six
public import CFSG.HardMathSupport.Foote.Coordinator.AnisoCube.OrderSix
public import CFSG.HardMathSupport.Foote.Coordinator.AnisoCube.Skeleton

public noncomputable section

namespace CFSG.HardMathSupport.Lang.TwE6Step3

open CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.RankThree.E6 CFSG.RankThree.Lattice
  CFSG.LocalAnalysis.ComponentInitial CFSG.LocalAnalysis.ComponentInitial.FourGroupChevalley
  CFSG.RankThree.PartOne.KE CFSG.RankThree.PartOne.KE6 CFSG.RankThree.Classical2
  CFSG.LieType.SeitzGeneration CFSG.Open CFSG.AGLEmbedding

theorem exists_cube_containing_plane {C : Type*} [Group C] [Finite C] {p : ℕ} [hp : Fact p.Prime]
    (hcomm : ∀ Q : Subgroup C, IsPGroup p Q → ∀ a ∈ Q, ∀ b ∈ Q, a * b = b * a)
    {E' E₀ : Subgroup C} (hE' : IsElemAbelian p E') (hE'c : Nat.card E' = p ^ 2)
    (hE₀ : IsElemAbelian p E₀) (hE₀c : Nat.card E₀ = p ^ 3) :
    ∃ E : Subgroup C, E' ≤ E ∧ IsElemAbelian p E ∧ Nat.card E = p ^ 3 := by
  classical
  have hpg : ∀ {F : Subgroup C}, IsElemAbelian p F → IsPGroup p F := fun {F} hF x =>
    ⟨1, by
      apply Subtype.ext
      simpa using hF.2 x x.2⟩
  obtain ⟨S, hS⟩ := (hpg hE').exists_le_sylow
  obtain ⟨S₀, hS₀⟩ := (hpg hE₀).exists_le_sylow
  obtain ⟨g, hg⟩ := MulAction.exists_smul_eq C S S₀
  have hSab : ∀ a ∈ (S : Subgroup C), ∀ b ∈ (S : Subgroup C), a * b = b * a :=
    hcomm S S.isPGroup'
  set E'' : Subgroup C := E₀.map (MulAut.conj g⁻¹).toMonoidHom with hE''
  have hE''S : E'' ≤ S := by
    rintro _ ⟨x, hx, rfl⟩
    have hx0 : x ∈ (S₀ : Subgroup C) := hS₀ hx
    rw [← hg, Sylow.coe_subgroup_smul, Subgroup.mem_smul_pointwise_iff_exists] at hx0
    obtain ⟨y, hy, hyx⟩ := hx0
    have hyx' : g * y * g⁻¹ = x := by simpa [MulAut.smul_def] using hyx
    have : g⁻¹ * x * g = y := by rw [← hyx']; group
    have h2 : g⁻¹ * x * g⁻¹⁻¹ = y := by simpa using this
    show g⁻¹ * x * g⁻¹⁻¹ ∈ S
    rw [h2]
    exact hy
  have hE''c : Nat.card E'' = p ^ 3 := by
    rw [hE'', Subgroup.card_map_of_injective (MulAut.conj g⁻¹).injective, hE₀c]
  let Ω : Subgroup C :=
    { carrier := {x | x ∈ (S : Subgroup C) ∧ x ^ p = 1}
      mul_mem' := fun {a b} ha hb => ⟨mul_mem ha.1 hb.1, by
        rw [(show Commute a b from hSab a ha.1 b hb.1).mul_pow, ha.2, hb.2, one_mul]⟩
      one_mem' := ⟨one_mem _, one_pow _⟩
      inv_mem' := fun {a} ha => ⟨inv_mem ha.1, by rw [inv_pow, ha.2, inv_one]⟩ }
  have hE'Ω : E' ≤ Ω := fun x hx => ⟨hS hx, hE'.2 x hx⟩
  have hE''Ω : E'' ≤ Ω := by
    rintro _ ⟨y, hy, rfl⟩
    refine ⟨hE''S ⟨y, hy, rfl⟩, ?_⟩
    rw [← map_pow, hE₀.2 y hy, map_one]
  have hdvd : p ^ 3 ∣ Nat.card Ω := by
    rw [← hE''c]
    exact Subgroup.card_dvd_of_le hE''Ω
  have hH : Nat.card (E'.subgroupOf Ω) = p ^ 2 := by
    rw [← hE'c]
    exact Nat.card_congr (Subgroup.subgroupOfEquivOfLe hE'Ω).toEquiv
  obtain ⟨K, hK, hHK⟩ := Sylow.exists_subgroup_card_pow_prime_le p hdvd (E'.subgroupOf Ω) hH
    (by norm_num : 2 ≤ 3)
  have hKcomm : ∀ x ∈ K.map Ω.subtype, ∀ y ∈ K.map Ω.subtype, x * y = y * x := by
    rintro _ ⟨a, -, rfl⟩ _ ⟨b, -, rfl⟩
    exact hSab a a.2.1 b b.2.1
  refine ⟨K.map Ω.subtype, fun x hx => ⟨⟨x, hE'Ω hx⟩, hHK hx, rfl⟩,
    ⟨IsMulCommutative.of_comm fun a b => Subtype.ext (hKcomm a a.2 b b.2), ?_⟩, ?_⟩
  · rintro _ ⟨a, -, rfl⟩
    exact a.2.2
  · rw [Subgroup.card_map_of_injective (Subgroup.subtype_injective Ω), hK]

section Main

set_option linter.unusedSectionVars false


theorem pSubgroup_comm_twistedE6 {ℓ f : ℕ} (hℓ : ℓ.Prime) (hf : 1 ≤ f) (K : Type) [Field K]
    (hK : Nat.card K = (ℓ ^ f) ^ 2) (σ : K ≃+* K) (hσ : ∀ c, σ c = c ^ (ℓ ^ f))
    {p : ℕ} (hp : p.Prime) (hp3 : 3 < p)
    (hpq : (p : ℤ) ∣ ((ℓ ^ f : ℕ) : ℤ) ^ 2 - ((ℓ ^ f : ℕ) : ℤ) + 1) :
    ∀ Q : Subgroup (twistedE6RootGroup K σ), IsPGroup p Q → ∀ a ∈ Q, ∀ b ∈ Q, a * b = b * a := by
  classical
  intro Q hQ a ha b hb
  have : Fact ℓ.Prime := ⟨hℓ⟩
  have hK0 : Nat.card K ≠ 0 := by
    rw [hK]
    exact pow_ne_zero _ (pow_ne_zero _ hℓ.ne_zero)
  have : Finite K := Nat.finite_of_card_ne_zero hK0
  have : Fintype K := Fintype.ofFinite K
  have : CharP K ℓ := charP_of_card_eq_prime_pow (f := f * 2)
    (by rw [← Nat.card_eq_fintype_card, hK, ← pow_mul])
  let L := AlgebraicClosure K
  have : CharP L ℓ := charP_of_injective_algebraMap (algebraMap K L).injective ℓ
  obtain ⟨g0, -, -, -, hconj⟩ := CFSG.RankThree.PartOne.KE6.tw6_frame K hf hK σ hσ hp hp3 hpq L
  obtain ⟨c, hc⟩ := hconj Q hQ
  exact commute_of_psiT_commute (g0 := g0) (c := c)
    (CFSG.RankThree.PartOne.KE.torusGroup_comm (mem_twistedTorusOf.1 (hc a ha)).1
      (mem_twistedTorusOf.1 (hc b hb)).1)

theorem excCubeHighAt_twistedE6_six_of_lines (h : TwE6SixLines) :
    CFSG.HardMathSupport.Malle.SeitzCube.ExcCubeHighAt TauCeti.LieTypeIndex.twistedE6 6 := by
  classical
  rintro q hv p hp hp2 hpq - hnd hord ⟨E₀, hE₀, hE₀c⟩
  have : Fact p.Prime := ⟨hp⟩
  have : Fact q.p.Prime := ⟨q.prime_p⟩
  obtain ⟨h6, hp3⟩ :=
    CFSG.HardMathSupport.Foote.Coordinator.AnisoCube.dvd_sq_sub_add_one_of_orderOf_eq_six hp hord
  have hp3' : 3 < p := by
    have := hp.two_le
    rcases (by omega : p = 2 ∨ p = 3 ∨ p = 4 ∨ 5 ≤ p) with h' | h' | h' | h'
    · exact absurd h' hp2
    · exact absurd h' hp3
    · exact absurd (h' ▸ hp) (by norm_num)
    · omega
  have hcard : q.card = q.p ^ q.exponent := TauCeti.PrimePower.card_def q
  have hpq' : ¬ p ∣ q.card := by
    intro hd
    rw [hcard] at hd
    exact hpq ((Nat.prime_dvd_prime_iff_eq hp q.prime_p).1 (hp.dvd_of_dvd_pow hd))
  have hpqZ : (p : ℤ) ∣ ((q.p ^ q.exponent : ℕ) : ℤ) ^ 2 - ((q.p ^ q.exponent : ℕ) : ℤ) + 1 := by
    rw [← hcard]
    have h1 := Int.natCast_dvd_natCast.2 h6
    have h2 : ((q.card ^ 2 - q.card + 1 : ℕ) : ℤ) = (q.card : ℤ) ^ 2 - q.card + 1 := by
      rw [Nat.cast_add, Nat.cast_sub (Nat.le_self_pow two_ne_zero q.card), Nat.cast_pow,
        Nat.cast_one]
    rwa [h2] at h1
  obtain ⟨K, _, σ, hK, hσ, ⟨e⟩⟩ := exists_catEquiv_twistedE6 q hv
  have : Finite (ModGL TwistTag.E6.tag K) := by
    have hK0 : Nat.card K ≠ 0 := by
      rw [hK]
      exact pow_ne_zero _ (pow_ne_zero _ q.prime_p.ne_zero)
    have : Finite K := Nat.finite_of_card_ne_zero hK0
    have : Fintype K := Fintype.ofFinite K
    exact finite_modGL
  have : Finite (Cat ⟨.twistedE6 q, hv⟩) :=
    Finite.of_equiv (twistedE6RootGroup K σ) e.symm.toEquiv
  have hcommCat : ∀ Q : Subgroup (Cat ⟨.twistedE6 q, hv⟩), IsPGroup p Q →
      ∀ a ∈ Q, ∀ b ∈ Q, a * b = b * a := by
    intro Q hQ a ha b hb
    have hQ' : IsPGroup p (Q.map e.toMonoidHom) := hQ.map _
    have hab := pSubgroup_comm_twistedE6 q.prime_p q.exponent_pos K hK σ hσ hp hp3' hpqZ
      (Q.map e.toMonoidHom) hQ' (e a) ⟨a, ha, rfl⟩ (e b) ⟨b, hb, rfl⟩
    exact e.injective (by simpa using hab)
  obtain ⟨E, R, hE, hEc, hRne, hRp, hEN⟩ := CFSG.HardMathSupport.Lang.SeitzPlane.exists_plane_twistedE6RootGroup_six
    q.prime_p q.exponent_pos K hK σ hσ hp hp3' (by rw [← hcard]; exact hpq')
    (by rw [← hcard]; exact hord) (by rw [← hcard]; exact hnd)
  let f : twistedE6RootGroup K σ →* Cat ⟨.twistedE6 q, hv⟩ := e.symm.toMonoidHom
  have hf : Function.Injective f := e.symm.injective
  have hE₀' : IsElemAbelian p (E.map f) :=
    CFSG.PreuniquenessRankFour.Helpers.elementary_abelian_map p hE f
  have hE₀c' : Nat.card (E.map f) = p ^ 2 := by
    rw [Subgroup.card_map_of_injective hf, hEc]
  have hN : ∀ x ∈ E.map f, (R.map f).map (MulAut.conj x).toMonoidHom = R.map f := by
    rintro _ ⟨x, hx, rfl⟩
    ext z
    constructor
    · rintro ⟨_, ⟨y, hy, rfl⟩, rfl⟩
      have hy' : x * y * x⁻¹ ∈ R := by
        rw [← hEN x hx]
        exact ⟨y, hy, rfl⟩
      exact ⟨x * y * x⁻¹, hy', by simp [MulAut.conj_apply, f]⟩
    · rintro ⟨y, hy, rfl⟩
      have hy' : x⁻¹ * y * x ∈ R := by
        have := hEN x⁻¹ (inv_mem hx)
        rw [← this]
        exact ⟨y, hy, by simp⟩
      refine ⟨f (x⁻¹ * y * x), ⟨_, hy', rfl⟩, ?_⟩
      simp [MulAut.conj_apply, f, mul_assoc]
  have hE'1 : E.map f ≠ ⊥ := by
    intro hbot
    have := hE₀c'
    rw [hbot, Subgroup.card_bot] at this
    have h2 : 1 < p ^ 2 := Nat.one_lt_pow two_ne_zero hp.one_lt
    omega
  have hHy : HyperGen p ⊤ (E.map f) := by
    refine seitzExcParabolicHyperTw ⟨TauCeti.LieTypeIndex.twistedE6 q, hv⟩ p hp
      (by rw [TauCeti.LieTypeIndex.characteristic_twistedE6]; exact hpq) (Or.inr ⟨q, rfl⟩) _ hE₀'
      hE'1 ⟨R.map f, ?_, ?_, hN⟩
    · rwa [Ne, Subgroup.map_eq_bot_iff_of_injective _ hf]
    · rw [TauCeti.LieTypeIndex.characteristic_twistedE6]
      exact hRp.map f
  obtain ⟨E₁, hle, hE₁, hE₁c⟩ := exists_cube_containing_plane hcommCat hE₀' hE₀c' hE₀ hE₀c
  refine ⟨E₁, hE₁, hE₁c, Or.inr ?_⟩
  refine CFSG.HardMathSupport.Foote.Coordinator.AnisoCube.hyperGen_of_hyperGen_of_le hHy ?_
  intro B hB hBi k hk
  have hBne : B ≠ ⊥ := by
    intro hbot
    rw [hbot, Subgroup.relIndex_bot_left, hE₀c'] at hBi
    have h1 : p ^ 2 = p ^ 1 := by rw [hBi, pow_one]
    have := Nat.pow_right_injective hp.two_le h1
    omega
  obtain ⟨y, hy⟩ := Subgroup.ne_bot_iff_exists_ne_one.1 hBne
  exact h q hv p hp hp3 hpq hord E₁ hE₁ hE₁c y (hle (hB y.2)) (fun h1 => hy (Subtype.ext h1))
    k (hk y y.2).symm

end Main

end CFSG.HardMathSupport.Lang.TwE6Step3
