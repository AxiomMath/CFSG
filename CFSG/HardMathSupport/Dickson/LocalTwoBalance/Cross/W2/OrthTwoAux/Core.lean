module

public import CFSG.HardMathSupport.Dickson.LocalTwoBalance.Cross.W2.OrthTwoAux.Cover
public import CFSG.HardMathSupport.Dickson.LocalTwoBalance.Cross.W2.OrthTwoAux.Refl

public section

namespace CFSG.HardMathSupport.Dickson.LocalTwoBalance.Cross.W2.OrthTwoAux

open CFSG.Open CFSG.HardMathSupport.Solomon.LocalBalance Polynomial Module
  CFSG.RankThree.PartOne CFSG.RankThree.PartOne.KCPrimary CFSG.RankThree.PartOne.KCOrthogonal
  CFSG.RankThree.Classical2 CFSG.RankThree.Classical CFSG.ClassicalGroups.Orthogonal
  CFSG.HardMathSupport.Timmesfeld.CrossChar
open CFSG.RankThree.OrthogonalInvolutions (commSpace mem_commSpace sub_mem_commSpace)

variable {K : Type} [Field K] [Finite K] {V : Type} [AddCommGroup V] [Module K V]
  [FiniteDimensional K V] {Q : QuadraticForm K V}

theorem orth2_eq_one_of_isometry_two (hK : Nat.card K = 2)
    (hQ : (QuadraticMap.polarBilin Q).Nondegenerate)
    (hT : ∃ U : Submodule K V, finrank K U = 3 ∧ ∀ u ∈ U, Q u = 0) (h8 : 8 ≤ finrank K V)
    {D : Subgroup (MulAut (ProjOrthDerived Q))} (hD : IsElemAbelian 3 D)
    (hcard : Nat.card D = 3 ^ 2) (hDinn : D ≤ innerAut (ProjOrthDerived Q))
    {H : Subgroup (MulAut (ProjOrthDerived Q))} (hH : innerAut (ProjOrthDerived Q) ≤ H)
    {g : MulAut (ProjOrthDerived Q)} (hg : g ∈ localDeltaIn 3 H D) {G : V ≃ₗ[K] V}
    (hGO : G ∈ TauCeti.QuadraticMap.orthogonalGroup Q)
    (hGg : ∀ y : orthDerived Q, g (QuotientGroup.mk y) = QuotientGroup.mk
      (⟨G * (y : V ≃ₗ[K] V) * G⁻¹, conj_mem_orthDerived hGO y.2⟩ : orthDerived Q)) :
    g = 1 := by
  classical
  have hp : Nat.Prime 3 := Nat.prime_three
  have : Fact (Nat.Prime 3) := ⟨hp⟩
  have : CharP K 2 := charP_two_of_card hK
  have : Finite V := Module.finite_of_finite K
  have hpl : (3 : ℕ) ≠ ringChar K := by rw [ringChar_eq_two_of_card hK]; norm_num
  have h2 : ∀ v : V, v + v = 0 := two_smul_eq_zero K
  obtain ⟨-, -, -, hsimple, hnonab, -, -, -, -⟩ :=
    orthogonal_high_Witt_derived_quotient_and_odd_lifts hQ hT
  have hcenter : Subgroup.center (ProjOrthDerived Q) = ⊥ := by
    rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal (Subgroup.center (ProjOrthDerived Q)) with
      h | h
    · exact h
    · exfalso
      obtain ⟨c, d, hcd⟩ := hnonab
      exact hcd (Subgroup.mem_center_iff.mp (h ▸ Subgroup.mem_top d) c)
  have hinj : Function.Injective
      (MulAut.conj : ProjOrthDerived Q →* MulAut (ProjOrthDerived Q)) :=
    conj_injective_of_center_bot' hcenter
  have hmk := mk_injective_of_card_two (Q := Q) hK
  set ι : orthDerived Q →* MulAut (ProjOrthDerived Q) :=
    (MulAut.conj : ProjOrthDerived Q →* MulAut (ProjOrthDerived Q)).comp
      (QuotientGroup.mk' ((scalars K V).subgroupOf (orthDerived Q))) with hιdef
  have hι : Function.Injective ι := hinj.comp hmk
  have hιapp : ∀ y : orthDerived Q, ι y = MulAut.conj (QuotientGroup.mk y : ProjOrthDerived Q) :=
    fun y => rfl
  have hDι : D ≤ ι.range := by
    intro d hd
    obtain ⟨t, ht⟩ := hDinn hd
    obtain ⟨y, rfl⟩ := QuotientGroup.mk_surjective t
    exact ⟨y, ht⟩
  set Dh : Subgroup (orthDerived Q) := D.comap ι with hDh
  have hmemDh : ∀ x, x ∈ Dh ↔ ι x ∈ D := fun x => Iff.rfl
  have hDhcard : Nat.card Dh = 9 := by
    rw [← Subgroup.card_map_of_injective hι, Subgroup.map_comap_eq_self hDι, hcard]
    norm_num
  have hDh3 : ∀ x ∈ Dh, x ^ 3 = 1 := fun x hx => by
    apply hι
    rw [map_pow, map_one]
    exact hD.2 _ ((hmemDh x).1 hx)
  have hDhcomm : ∀ x ∈ Dh, ∀ y ∈ Dh, x * y = y * x := fun x hx y hy => by
    apply hι
    rw [map_mul, map_mul]
    exact congrArg Subtype.val (hD.1.is_comm.comm ⟨_, (hmemDh x).1 hx⟩ ⟨_, (hmemDh y).1 hy⟩)
  let _ : CommGroup Dh := { (inferInstance : Group Dh) with
    mul_comm := fun a b => Subtype.ext (hDhcomm a a.2 b b.2) }
  obtain ⟨e⟩ := exists_mulEquiv_z3_two (G := Dh) (fun g => Subtype.ext (hDh3 g g.2))
    (by rw [hDhcard])
  let πa : Z3 →+ (Fin 2 → ZMod 3) :=
    { toFun := fun z => ![z 0, z 1]
      map_zero' := by
        ext i
        fin_cases i <;> rfl
      map_add' := fun a b => by
        ext i
        fin_cases i <;> rfl }
  let π : Multiplicative Z3 →* Multiplicative (Fin 2 → ZMod 3) := πa.toMultiplicative
  set xh : Z3 → orthDerived Q :=
    fun z => ((e.symm (π (Multiplicative.ofAdd z)) : Dh) : orthDerived Q) with hxh
  have hxhD : ∀ z, xh z ∈ Dh := fun z => (e.symm (π (Multiplicative.ofAdd z))).2
  let ρ : Multiplicative Z3 →* Module.End K V :=
    LinearEquiv.automorphismGroup.toLinearMapMonoidHom.comp
      ((orthDerived Q).subtype.comp (Dh.subtype.comp (e.symm.toMonoidHom.comp π)))
  have hact : ∀ z v, act ρ z v = (xh z : V ≃ₗ[K] V) v := fun z v => rfl
  have hxh1 : ∀ z : Z3, (z 0 ≠ 0 ∨ z 1 ≠ 0) → xh z ≠ 1 := by
    intro z hz h1
    have h3 : e.symm (π (Multiplicative.ofAdd z)) = 1 := Subtype.ext h1
    have h4 : π (Multiplicative.ofAdd z) = 1 := by simpa using h3
    have h5 : (![z 0, z 1] : Fin 2 → ZMod 3) = 0 := h4
    rcases hz with hz | hz
    · exact hz (congrFun h5 0)
    · exact hz (congrFun h5 1)
  have hz₃ : act ρ ![0, 0, 1] = 1 := by
    have h1 : π (Multiplicative.ofAdd ![0, 0, 1]) = 1 := by
      show Multiplicative.ofAdd (πa ![0, 0, 1]) = 1
      rw [ofAdd_eq_one]
      ext i
      fin_cases i <;> rfl
    show ρ (Multiplicative.ofAdd ![0, 0, 1]) = 1
    simp only [ρ, MonoidHom.comp_apply, h1, map_one]
  have hxhO : ∀ z, (xh z : V ≃ₗ[K] V) ∈ TauCeti.QuadraticMap.orthogonalGroup Q :=
    fun z => orthDerived_le_orthogonalGroup Q (xh z).2
  have hisoB : ∀ z u v, QuadraticMap.polarBilin Q (act ρ z u) (act ρ z v) =
      QuadraticMap.polarBilin Q u v := fun z u v => by
    rw [QuadraticMap.polarBilin_apply_apply, QuadraticMap.polarBilin_apply_apply, hact, hact]
    exact TauCeti.QuadraticMap.polar_apply_of_mem_orthogonalGroup (hxhO z) u v
  have hpN : ∀ φ ∈ Rset, Even (finrank K (fixOf ρ {x | dot φ x = 0})) := fun φ hφ =>
    even_finrank_fixOf_N (CFSG.AGLEmbedding.polarBilin_isAlt_of_charTwo Q) hQ ρ hisoB hφ
  have hp0 : Even (finrank K (fixOf ρ Set.univ)) := by
    have hodd : Odd (Nat.card (⊤ : AddSubgroup Z3)) := by
      rw [AddSubgroup.card_top, Nat.card_eq_fintype_card, Fintype.card_fun, ZMod.card,
        Fintype.card_fin]
      decide
    have h := even_finrank_fixOf (CFSG.AGLEmbedding.polarBilin_isAlt_of_charTwo Q) hQ ρ hisoB ⊤
      hodd
    rwa [AddSubgroup.coe_top] at h
  have hGcomm : ∀ z, G * (xh z : V ≃ₗ[K] V) = (xh z : V ≃ₗ[K] V) * G := by
    intro z
    have hc := commute_of_mem_localDeltaIn hg ((hmemDh (xh z)).1 (hxhD z))
    have h1 : MulAut.conj (g (QuotientGroup.mk (xh z))) =
        MulAut.conj (QuotientGroup.mk (xh z) : ProjOrthDerived Q) := by
      rw [← mul_conj_mul_inv, ← hιapp, hc, mul_assoc, mul_inv_cancel, mul_one]
    have h2' := hinj h1
    rw [hGg] at h2'
    have h3 : G * (xh z : V ≃ₗ[K] V) * G⁻¹ = xh z := congrArg Subtype.val (hmk h2')
    calc G * (xh z : V ≃ₗ[K] V) = G * (xh z : V ≃ₗ[K] V) * G⁻¹ * G := by group
      _ = (xh z : V ≃ₗ[K] V) * G := by rw [h3]
  have hGact : ∀ z v, G (act ρ z v) = act ρ z (G v) := fun z v => by
    rw [hact, hact]
    exact congrArg (fun f : V ≃ₗ[K] V => f v) (hGcomm z)
  have hgk : Nat.Coprime 3 (orderOf g) := by
    refine coprime_orderOf_of_mem_localDeltaIn hp hg ((hmemDh _).1 (hxhD ![1, 0, 0])) ?_
    intro h1
    exact hxh1 ![1, 0, 0] (Or.inl e1_ne_zero) (hι (h1.trans (map_one ι).symm))
  have hGk : G ^ orderOf g = 1 :=
    orth2_isometry_eq_one hK hQ (by omega) (pow_mem hGO _)
      (orth2_conj_eq_of_eq_one hK (pow_mem hGO _) (orth2_conj_pow hGO hGg _)
        (pow_orderOf_eq_one g))
  have hGpow : ∀ (n : ℕ) (w : V), ((G : V →ₗ[K] V) ^ n) w = (G ^ n) w := by
    intro n
    induction n with
    | zero => intro w; rfl
    | succ n ih =>
      intro w
      rw [pow_succ', Module.End.mul_apply, ih w, pow_succ', LinearEquiv.mul_apply]
      rfl
  have hGk' : ∀ w : V, ((G : V →ₗ[K] V) ^ orderOf g) w = w := fun w => by
    rw [hGpow, hGk]
    rfl
  have hfixeq : ∀ z : Z3, fixedSpace (xh z : V ≃ₗ[K] V) = fixOf ρ {z} := by
    intro z
    refine Submodule.ext fun w => ?_
    rw [mem_fixedSpace, mem_fixOf]
    constructor
    · intro hw x hx
      rw [Set.mem_singleton_iff] at hx
      rw [hx, hact]
      exact hw
    · intro hw
      rw [← hact]
      exact hw z rfl
  have hfixV : ∀ z : Z3, (z 0 ≠ 0 ∨ z 1 ≠ 0) → GoodSix ρ z → ∀ v ∈ fixOf ρ {z}, G v = v := by
    intro z hz0 hz v hv
    obtain ⟨-, h6, y, u, hu, hyu⟩ := hz
    have hx3 : xh z ^ 3 = 1 := hDh3 _ (hxhD z)
    have hxo : orderOf (xh z) = 3 := orderOf_eq_prime hx3 (hxh1 z hz0)
    have hfix := hfixeq z
    have h6' : 6 ≤ finrank K (fixedSpace (xh z : V ≃ₗ[K] V)) := by
      rw [hfix]
      exact h6
    have hyM : (xh y : V ≃ₗ[K] V) ∈ isometryCentralizer Q (xh z : V ≃ₗ[K] V) := by
      rw [mem_isometryCentralizer]
      refine ⟨fun w => (TauCeti.QuadraticMap.mem_orthogonalGroup_iff).1 (hxhO y) w,
        fun w => ?_⟩
      have := congrArg (fun t : orthDerived Q => (t : V ≃ₗ[K] V) w)
        (hDhcomm _ (hxhD y) _ (hxhD z))
      simpa using this
    have hy3 : (xh y : V ≃ₗ[K] V) ^ 3 = 1 := by
      have := congrArg (fun t : orthDerived Q => (t : V ≃ₗ[K] V)) (hDh3 _ (hxhD y))
      simpa using this
    exact orth2_fixes_fixedSpace_of_mem_delta hK hQ hT hinj hH hg (xh z) hxo
      ((hmemDh _).1 (hxhD z)) h6' hyM hy3 (by rw [hfix]; exact hu)
      (by rw [← hact]; exact hyu) hGO (hGcomm z) hGg v (by rw [hfix]; exact hv)
  have hfixU : ∀ z : Z3, (z 0 ≠ 0 ∨ z 1 ≠ 0) → 8 ≤ finrank K (LinearMap.ker (eCyc ρ z)) →
      ∀ v ∈ LinearMap.ker (eCyc ρ z), G v = v := by
    intro z hz0 hz8 v hv
    have hx3 : xh z ^ 3 = 1 := hDh3 _ (hxhD z)
    have hxo : orderOf (xh z) = 3 := orderOf_eq_prime hx3 (hxh1 z hz0)
    have hE : eCyc ρ z = (xh z : V ≃ₗ[K] V).toLinearMap ^ 2 +
        (xh z : V ≃ₗ[K] V).toLinearMap + 1 := by
      ext w
      simp only [eCyc, LinearMap.add_apply, act_zero, Module.End.one_apply, act_add,
        Module.End.mul_apply, hact, pow_two, LinearEquiv.coe_coe]
      abel
    have hker : LinearMap.ker (eCyc ρ z) =
        primaryComponent (xh z : V ≃ₗ[K] V).toLinearMap (cyc3 K) := by
      rw [primaryComponent, aeval_cyc3, hE]
    have h8' : 8 ≤ finrank K (primaryComponent (xh z : V ≃ₗ[K] V).toLinearMap (cyc3 K)) := by
      rw [← hker]
      exact hz8
    exact orth2_fixes_unitary hQ hT hK hinj hH hg (xh z) hxo ((hmemDh _).1 (hxhD z)) h8' hGO
      (hGcomm z) hmk hGg hgk hGk v (hker ▸ hv)
  have hrefl : ∀ z : Z3, (z 0 ≠ 0 ∨ z 1 ≠ 0) → 4 ≤ finrank K (fixOf ρ {z}) →
      commSpace G ≤ fixOf ρ {z} → finrank K (commSpace G) ≠ 1 := by
    intro z hz0 h4 hle
    have hx3 : xh z ^ 3 = 1 := hDh3 _ (hxhD z)
    have hxo : orderOf (xh z) = 3 := orderOf_eq_prime hx3 (hxh1 z hz0)
    have hfix := hfixeq z
    exact orth2_finrank_commSpace_ne_one hK hQ hT (by omega) hinj hH hg (xh z) hxo
      ((hmemDh _).1 (hxhD z)) (by rw [hfix]; exact h4) hGO hGg (by rw [hfix]; exact hle)
  have he1 : act ρ ![1, 0, 0] ≠ 1 := fun h1 => hxh1 ![1, 0, 0] (Or.inl e1_ne_zero)
    (Subtype.ext (LinearEquiv.ext fun w => by rw [← hact, h1]; rfl))
  have hall := rank_two_cover' hK ρ h8 hz₃ he1 hpN hp0 hGact hgk hGk' hrefl hfixV hfixU
  have hG : G = 1 := LinearEquiv.ext hall
  ext t
  obtain ⟨y, rfl⟩ := QuotientGroup.mk_surjective t
  rw [hGg y, MulAut.one_apply]
  congr 1
  apply Subtype.ext
  change G * (y : V ≃ₗ[K] V) * G⁻¹ = y
  rw [hG, one_mul, inv_one, mul_one]

end CFSG.HardMathSupport.Dickson.LocalTwoBalance.Cross.W2.OrthTwoAux
