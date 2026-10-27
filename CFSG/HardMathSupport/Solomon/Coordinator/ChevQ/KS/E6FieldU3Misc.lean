module

public import CFSG.HardMathSupport.Solomon.Coordinator.ChevQ.KS.E6Field

public section

namespace CFSG.HardMathSupport.Solomon.Coordinator.ChevQ

namespace KSFourU

open CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley

theorem exists_mulAut_range_restrict {G H : Type*} [Group G] [Group H] (p : G →* H)
    (ϕ₀ : H →* H) (hϕ : Function.Injective ϕ₀) (α : MulAut G)
    (hα : ∀ g, p (α g) = ϕ₀ (p g)) :
    ∃ β : MulAut ↥p.range, (∀ r : ↥p.range, ((β r : ↥p.range) : H) = ϕ₀ (r : H)) ∧
      ∀ n : ℕ, α ^ n = 1 → β ^ n = 1 := by
  have hmaps : ∀ r : H, r ∈ p.range → ϕ₀ r ∈ p.range := by
    rintro _ ⟨g, rfl⟩
    rw [← hα g]
    exact ⟨α g, rfl⟩
  obtain ⟨f, hf⟩ : ∃ f : ↥p.range →* ↥p.range,
      ∀ r : ↥p.range, ((f r : ↥p.range) : H) = ϕ₀ (r : H) :=
    ⟨{ toFun := fun r => ⟨ϕ₀ (r : H), hmaps _ r.2⟩
       map_one' := Subtype.ext (by simp)
       map_mul' := fun a b => Subtype.ext (by simp) }, fun r => rfl⟩
  have hinj : Function.Injective f := by
    intro a b hab
    apply Subtype.ext
    apply hϕ
    rw [← hf a, ← hf b]
    exact congrArg Subtype.val hab
  have hsurj : Function.Surjective f := by
    intro y
    obtain ⟨g, hg⟩ := y.2
    have hαg : α (MulEquiv.symm α g) = g := MulEquiv.apply_symm_apply α g
    refine ⟨⟨p (MulEquiv.symm α g), ⟨MulEquiv.symm α g, rfl⟩⟩, Subtype.ext ?_⟩
    rw [hf]
    show ϕ₀ (p (MulEquiv.symm α g)) = (y : H)
    rw [← hα, hαg, hg]
  have hpow : ∀ β : MulAut ↥p.range,
      (∀ r : ↥p.range, ((β r : ↥p.range) : H) = ϕ₀ (r : H)) →
        ∀ n : ℕ, ∀ g : G, ((β ^ n) ⟨p g, ⟨g, rfl⟩⟩ : H) = p ((α ^ n) g) := by
    intro β hβ n
    induction n with
    | zero => intro g; simp
    | succ n ih =>
      intro g
      rw [pow_succ' β n, pow_succ' α n, MulAut.mul_apply, MulAut.mul_apply, hβ, ih g, ← hα]
  refine ⟨MulEquiv.ofBijective f ⟨hinj, hsurj⟩, fun r => hf r, ?_⟩
  intro n hn
  refine MulEquiv.ext fun x => ?_
  obtain ⟨g, hg⟩ := x.2
  have hx : x = ⟨p g, ⟨g, rfl⟩⟩ := Subtype.ext hg.symm
  rw [hx, MulAut.one_apply]
  apply Subtype.ext
  rw [hpow (MulEquiv.ofBijective f ⟨hinj, hsurj⟩) (fun r => hf r) n g, hn, MulAut.one_apply]

theorem end_ext_single_field {L : Type} [Field L] {τ : Tag}
    {f g : Module.End L (RootModule τ L)}
    (h : ∀ b : Label τ, f (Finsupp.single b 1) = g (Finsupp.single b 1)) : f = g :=
  Finsupp.lhom_ext' fun b => LinearMap.ext_ring (h b)

theorem entrywiseHom_single_apply {R : Type} [CommRing R] {τ : Tag} (σ : R →+* R)
    (A : Module.End R (RootModule τ R)) (b : Label τ) :
    entrywiseHom σ A (Finsupp.single b 1) =
      Finsupp.mapRange σ σ.map_zero (A (Finsupp.single b 1)) :=
  entrywise_single σ A b

theorem mapRange_entrywise_comm {K L : Type} [Field K] [Field L] (ι : K →+* L)
    (η : K →+* K) (η' : L →+* L) (hcomm : ∀ c, η' (ι c) = ι (η c)) {ν : Type} (v : ν →₀ K) :
    Finsupp.mapRange ι ι.map_zero (Finsupp.mapRange η η.map_zero v) =
      Finsupp.mapRange η' η'.map_zero (Finsupp.mapRange ι ι.map_zero v) := by
  ext c
  simp [Finsupp.mapRange_apply, hcomm]

theorem baseChangeGL_entrywise_comm
    {τ : Tag} {K L : Type} [Field K] [Field L] (ι : K →+* L)
    (η : K →+* K) (η' : L →+* L) (hcomm : ∀ c, η' (ι c) = ι (η c)) (x : ModGL τ K) :
    baseChangeGL ι (Units.map (entrywiseHom η) x) =
      Units.map (entrywiseHom η') (baseChangeGL ι x) := by
  refine Units.ext (end_ext_single_field fun b => ?_)
  rw [baseChangeGL_apply_single, Units.coe_map, Units.coe_map, entrywiseHom_single_apply,
    entrywiseHom_single_apply, baseChangeGL_apply_single]
  exact mapRange_entrywise_comm ι η η' hcomm _

theorem exists_order_nine_unit_of_fieldAut {K L : Type} [Field K] [Finite K] [Field L]
    [Algebra K L] (hK : Nat.card K = 64) {η : K ≃+* K} (hη1 : η ≠ 1)
    (hηodd : Odd (orderOf η)) (η' : L ≃+* L)
    (hcomm : ∀ c : K, η' (algebraMap K L c) = algebraMap K L (η c)) :
    ∃ ζ : Lˣ, orderOf ζ = 9 ∧ (Units.map η'.toRingHom.toMonoidHom ζ = ζ ^ 4 ∨
      Units.map η'.toRingHom.toMonoidHom ζ = ζ ^ 7) := by
  have hη3 : orderOf η = 3 :=
    orderOf_eq_three_of_odd_ringAut (hK.trans (by norm_num)) hη1 hηodd
  have hηpow : η ^ 3 = 1 := by
    rw [← hη3]
    exact pow_orderOf_eq_one η
  obtain ⟨d, T, -, hd3, hT, -, hησT⟩ :=
    CFSG.HardMathSupport.Lang.E6Descent.exists_frobenius_of_cube Nat.prime_two (f := 6)
      (by norm_num) K (hK.trans (by norm_num)) η hηpow hη1
  have hd : d = 2 := by omega
  subst hd
  have hTx : ∀ x : K, T x = x ^ 4 := fun x => (hT x).trans (by norm_num)
  have hηx : (∀ x : K, η x = x ^ 4) ∨ (∀ x : K, η x = x ^ 16) := by
    rcases hησT with h | h
    · exact Or.inl fun x => by rw [h]; exact hTx x
    · refine Or.inr fun x => ?_
      have hT2 : (T ^ 2) x = T (T x) := by rw [pow_two]; rfl
      rw [h, hT2, hTx, hTx, ← pow_mul]
  have hcardU : Nat.card Kˣ = 63 := by
    rw [Nat.card_units, hK]
  obtain ⟨g, hg⟩ := IsCyclic.exists_ofOrder_eq_natCard (α := Kˣ)
  rw [hcardU] at hg
  have h7 : (7 : ℕ) ∣ orderOf g := by
    rw [hg]
    norm_num
  have hord7 : orderOf (g ^ 7) = 9 := by
    have h := orderOf_pow_of_dvd (by norm_num : (7 : ℕ) ≠ 0) h7
    omega
  obtain ⟨ζ₀, hζ₀⟩ : ∃ z : Kˣ, orderOf z = 9 := ⟨g ^ 7, hord7⟩
  have hz9 : ζ₀ ^ 9 = 1 := by
    rw [← hζ₀]
    exact pow_orderOf_eq_one ζ₀
  have h16 : ζ₀ ^ 16 = ζ₀ ^ 7 := by
    rw [show (16 : ℕ) = 7 + 9 by norm_num, pow_add, hz9, mul_one]
  have hinj : Function.Injective (Units.map (algebraMap K L).toMonoidHom) :=
    Units.map_injective (algebraMap K L).injective
  have hA : ∀ x : Kˣ, Units.map η'.toRingHom.toMonoidHom
      (Units.map (algebraMap K L).toMonoidHom x) =
        Units.map (algebraMap K L).toMonoidHom (Units.map η.toRingHom.toMonoidHom x) :=
    fun x => Units.ext (hcomm x)
  have hB4 : (∀ y : K, η y = y ^ 4) → ∀ x : Kˣ, Units.map η.toRingHom.toMonoidHom x = x ^ 4 :=
    fun h x => Units.ext (by rw [Units.val_pow_eq_pow_val]; exact h x)
  have hB16 : (∀ y : K, η y = y ^ 16) →
      ∀ x : Kˣ, Units.map η.toRingHom.toMonoidHom x = x ^ 16 :=
    fun h x => Units.ext (by rw [Units.val_pow_eq_pow_val]; exact h x)
  refine ⟨Units.map (algebraMap K L).toMonoidHom ζ₀, ?_, ?_⟩
  · exact (orderOf_injective _ hinj ζ₀).trans hζ₀
  · rcases hηx with hx | hx
    · left
      rw [hA ζ₀, hB4 hx ζ₀, map_pow]
    · right
      rw [hA ζ₀, hB16 hx ζ₀, h16, map_pow]

end KSFourU

end CFSG.HardMathSupport.Solomon.Coordinator.ChevQ

end
