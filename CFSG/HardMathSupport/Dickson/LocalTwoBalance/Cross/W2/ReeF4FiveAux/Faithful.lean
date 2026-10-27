module

public import CFSG.HardMathSupport.Dickson.LocalTwoBalance.Cross.W2.ReeF4FiveAux.Plane
public import CFSG.HardMathSupport.Dickson.LocalTwoBalance.Cross.W2.ReeF4FiveAux.Arith
public import CFSG.HardMathSupport.Timmesfeld.CrossChar.ExcFieldReeF4Core

public section

namespace CFSG.HardMathSupport.Dickson.LocalTwoBalance.Cross.W2.ReeF4FiveAux

open CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.LieType.Ree
  CFSG.RankThree.PartOne.KE CFSG.RankThree.PartOne.RF4 CFSG.RankThree.Chevalley
  CFSG.RankThree.PartOne.KLR CFSG.RankThree.PartOne.K1214 CFSG.RankThree.PartOne.K128
  CFSG.RankThree.PartOne
  CFSG.LocalAnalysis.ComponentInitial.FourGroupChevalley
  CFSG.HardMathSupport.Malle.LocalAction CFSG.HardMathSupport.Timmesfeld.CrossChar
  CFSG.HardMathSupport.Solomon.LocalBalance

section Suzuki

variable {a : ℕ} {K : Type} [Field K] [Finite K]

theorem suzuki_nonab (ha : 1 ≤ a) (hK : Nat.card K = 2 ^ (2 * a + 1)) :
    ∃ x y : suzukiGroup a K, x * y ≠ y * x := by
  obtain ⟨-, hnt, -⟩ := suzuki_simple ha hK
  obtain ⟨hc, -⟩ := suzuki_perfect ha hK
  by_contra h
  push Not at h
  have hb : commutator (suzukiGroup a K) = ⊥ := by
    rw [commutator_def, eq_bot_iff]
    refine Subgroup.commutator_le.2 fun g₁ _ g₂ _ => ?_
    rw [Subgroup.mem_bot]
    exact commutatorElement_eq_one_iff_mul_comm.2 (h g₁ g₂)
  rw [hc] at hb
  obtain ⟨g, hg⟩ := exists_ne (1 : suzukiGroup a K)
  have hg' : g ∈ (⊥ : Subgroup (suzukiGroup a K)) := hb ▸ Subgroup.mem_top g
  exact hg (Subgroup.mem_bot.1 hg')

theorem suzuki_quasisimple (ha : 1 ≤ a) (hK : Nat.card K = 2 ^ (2 * a + 1)) :
    CFSG.IsQuasisimple (suzukiGroup a K) ∧ Subgroup.center (suzukiGroup a K) = ⊥ := by
  haveI := (suzuki_simple ha hK).2.2
  exact CFSG.LocalCores.isQuasisimple_of_isSimpleGroup (suzuki_nonab ha hK)

end Suzuki

section Inner

theorem mem_sup_of_commute' {G : Type*} [Group G] {A B : Subgroup G}
    (h : ∀ a ∈ A, ∀ b ∈ B, a * b = b * a) {x : G} (hx : x ∈ A ⊔ B) :
    ∃ a ∈ A, ∃ b ∈ B, a * b = x := by
  let T : Subgroup G :=
    { carrier := {x | ∃ a ∈ A, ∃ b ∈ B, a * b = x}
      mul_mem' := by
        rintro _ _ ⟨a, ha, b, hb, rfl⟩ ⟨a', ha', b', hb', rfl⟩
        refine ⟨a * a', A.mul_mem ha ha', b * b', B.mul_mem hb hb', ?_⟩
        calc a * a' * (b * b') = a * (a' * b) * b' := by group
          _ = a * (b * a') * b' := by rw [h a' ha' b hb]
          _ = a * b * (a' * b') := by group
      one_mem' := ⟨1, A.one_mem, 1, B.one_mem, one_mul 1⟩
      inv_mem' := by
        rintro _ ⟨a, ha, b, hb, rfl⟩
        refine ⟨a⁻¹, A.inv_mem ha, b⁻¹, B.inv_mem hb, ?_⟩
        calc a⁻¹ * b⁻¹ = (b * a)⁻¹ := by group
          _ = (a * b)⁻¹ := by rw [← h a ha b hb] }
  have hle : A ⊔ B ≤ T := sup_le (fun a ha => ⟨a, ha, 1, B.one_mem, mul_one a⟩)
    (fun b hb => ⟨1, A.one_mem, b, hb, one_mul b⟩)
  exact hle hx

variable {K : Type} [Field K] [Finite K] [CharP K ReeTag.F4.prime] {a : ℕ}

theorem mem_rootsOfUnity_pow_five {L : Type} [Field L] {ξ : Lˣ} (hξ : IsPrimitiveRoot ξ 5)
    (s : ℕ) : ξ ^ s ∈ rootsOfUnity 5 L := by
  rw [mem_rootsOfUnity, ← pow_mul, mul_comm, pow_mul, hξ.pow_eq_one, one_pow]

@[expose] def planeElt {L : Type} [Field L] {ξ : Lˣ} (hξ : IsPrimitiveRoot ξ 5) (s t : ℕ) :
    (rootsOfUnity 5 L) × (rootsOfUnity 5 L) :=
  (⟨ξ ^ s, mem_rootsOfUnity_pow_five hξ s⟩, ⟨ξ ^ t, mem_rootsOfUnity_pow_five hξ t⟩)

theorem planeElt_ne_one {L : Type} [Field L] {ξ : Lˣ} (hξ : IsPrimitiveRoot ξ 5) {s t : ℕ}
    (h : (s : ZMod 5) ≠ 0 ∨ (t : ZMod 5) ≠ 0) : planeElt hξ s t ≠ 1 := by
  intro h1
  rcases h with h | h
  · apply h
    have h2 : ξ ^ s = 1 := congrArg (fun z : (rootsOfUnity 5 L) × (rootsOfUnity 5 L) =>
      ((z.1 : rootsOfUnity 5 L) : Lˣ)) h1
    rw [hξ.pow_eq_one_iff_dvd] at h2
    exact (ZMod.natCast_eq_zero_iff s 5).2 h2
  · apply h
    have h2 : ξ ^ t = 1 := congrArg (fun z : (rootsOfUnity 5 L) × (rootsOfUnity 5 L) =>
      ((z.2 : rootsOfUnity 5 L) : Lˣ)) h1
    rw [hξ.pow_eq_one_iff_dvd] at h2
    exact (ZMod.natCast_eq_zero_iff t 5).2 h2

theorem inner_eq_one (ha : 1 ≤ a) (hK : Nat.card K = 2 ^ (2 * a + 1)) (P : Plane5 K a)
    (u : ReeTag.F4.reeGamma K a) (hcomm : ∀ z, u * P.Ψ z = P.Ψ z * u)
    (hfix : ∀ z, z ≠ 1 → ∀ A Sg, IsDecomp P z A Sg → ∀ t ∈ Sg, u * t = t * u) : u = 1 := by
  classical
  have hL2 : CharP (AlgebraicClosure K) 2 :=
    charP_of_injective_algebraMap (algebraMap K (AlgebraicClosure K)).injective 2
  obtain ⟨ξ, hξ⟩ := exists_primitive_five (AlgebraicClosure K)
  have key : ∀ z : (rootsOfUnity 5 (AlgebraicClosure K)) × (rootsOfUnity 5 (AlgebraicClosure K)),
      z ≠ 1 → ∃ c : Fin ReeTag.F4.tag.rank → (AlgebraicClosure K)ˣ,
      (∀ β ∈ rootCharKernel (expTuple (z.1 : (AlgebraicClosure K)ˣ) (z.2 : (AlgebraicClosure K)ˣ)
        P.U), rootChar c β = 1) ∧ rootDiagUnit ReeTag.F4.tag c = reeConj P.g₀ u := by
    intro z hz
    obtain ⟨A, Sg, hd⟩ := plane5_decomp hK P z hz
    have hd' := hd
    obtain ⟨hAmem, hcAS, -, hsup, -, ⟨e⟩⟩ := hd'
    have huC : u ∈ A ⊔ Sg := by
      rw [hsup, Subgroup.mem_centralizer_singleton_iff]
      exact hcomm z
    obtain ⟨α, hαA, s, hsS, hαs⟩ := mem_sup_of_commute' hcAS huC
    have hsc : ∀ t ∈ Sg, s * t = t * s := by
      intro t ht
      have h1 := hfix z hz A Sg hd t ht
      have h2 := hcAS α hαA t ht
      rw [← hαs] at h1
      have h3 : α * (s * t) = α * (t * s) := by
        calc α * (s * t) = (α * s) * t := by rw [mul_assoc]
          _ = t * (α * s) := h1
          _ = (t * α) * s := by rw [mul_assoc]
          _ = (α * t) * s := by rw [← h2]
          _ = α * (t * s) := by rw [mul_assoc]
      exact mul_left_cancel h3
    have hs1 : s = 1 := by
      have hcen := (suzuki_quasisimple ha hK).2
      have hes : e ⟨s, hsS⟩ ∈ Subgroup.center (suzukiGroup a K) := by
        rw [Subgroup.mem_center_iff]
        intro y
        obtain ⟨t, rfl⟩ := e.surjective y
        rw [← map_mul, ← map_mul]
        congr 1
        exact Subtype.ext (hsc t t.2).symm
      rw [hcen, Subgroup.mem_bot, map_eq_one_iff _ e.injective] at hes
      exact congrArg Subtype.val hes
    have huA : u ∈ A := by
      rw [← hαs, hs1, mul_one]
      exact hαA
    obtain ⟨c, hc, hcu⟩ := mem_ZGrp.1 ((hAmem u).1 huA)
    exact ⟨c, hc, hcu⟩
  have hz₀ : planeElt hξ 1 0 ≠ 1 := planeElt_ne_one hξ (Or.inl (by decide))
  obtain ⟨c₀, -, hc₀⟩ := key _ hz₀
  have hroot : ∀ β ∈ rootFinset ReeTag.F4.tag, rootChar c₀ β = 1 := by
    intro β hβ
    obtain ⟨x, y, hxy, hβxy⟩ := P.hcov β hβ
    have hz : planeElt hξ x.val y.val ≠ 1 := planeElt_ne_one hξ (by simpa using hxy)
    obtain ⟨c, hc, hcu⟩ := key _ hz
    have hcc : c = c₀ := rootDiagUnit_injective (hcu.trans hc₀.symm)
    subst hcc
    refine hc β ?_
    have := rootCharKernel_expTuple_pow_five hξ P.U x.val y.val
    show β ∈ rootCharKernel (expTuple (ξ ^ x.val) (ξ ^ y.val) P.U)
    rw [this]
    simpa using hβxy
  have hc1 : c₀ = 1 := by
    funext i
    have h1 := hroot (Pi.single i 1) ((mem_rootFinset).2 (isRoot_single _ i))
    rw [CTTorus.rootChar_single] at h1
    exact h1
  apply reeConj_injective P.g₀
  rw [← hc₀, hc1, rootDiagUnit_one, map_one]

end Inner

section Outer

variable {K : Type} [Field K] [Finite K] [CharP K ReeTag.F4.prime] {a : ℕ}

theorem false_of_outer_prime_fix_suzuki (ha : 1 ≤ a) (hK : Nat.card K = 2 ^ (2 * a + 1))
    (T : Subgroup (ReeTag.F4.reeGamma K a)) (eT : T ≃* suzukiGroup a K) {r : ℕ} (hr : r.Prime)
    (hr5 : r ≠ 5) {h : MulAut (ReeTag.F4.reeGamma K a)} (hhr : h ^ r = 1)
    (hho : h ∉ innerAut (ReeTag.F4.reeGamma K a)) (hfix : ∀ t ∈ T, h t = t) : False := by
  have : Fact r.Prime := ⟨hr⟩
  obtain ⟨hNFex, hNFuniq⟩ := reeGamma_normalForm ha hK
  obtain ⟨-, hone, hpow, -⟩ := reeGammaFieldAut_hom_facts (K := K) (a := a)
  obtain ⟨u, β, rfl⟩ := hNFex h
  have hβr : β ^ r = 1 := by
    obtain ⟨z, hz⟩ : ∃ z, (MulAut.conj u * ReeTag.F4.reeGammaFieldAut K a β) ^ r =
        MulAut.conj z * ReeTag.F4.reeGammaFieldAut K a β ^ r :=
      ⟨_, CFSG.RankThree.PartOne.KE.conj_mul_pow_aut u (ReeTag.F4.reeGammaFieldAut K a β) r⟩
    have h' : MulAut.conj 1 * ReeTag.F4.reeGammaFieldAut K a 1 =
        MulAut.conj z * ReeTag.F4.reeGammaFieldAut K a (β ^ r) := by
      rw [map_one, hone, one_mul, hpow, ← hz, hhr]
    exact (hNFuniq _ _ _ _ h').2.symm
  have hβ1 : β ≠ 1 := by
    rintro rfl
    exact hho ⟨u, by rw [hone, mul_one]⟩
  have hβ : orderOf β = r := orderOf_eq_prime hβr hβ1
  obtain ⟨σ₁, -, -, -, hcardAut, -⟩ :=
    CFSG.LocalAnalysis.ComponentInitial.finite_field_automorphism_fixed_field_cardinality
      (F := K) Nat.prime_two (by omega) hK
  have hrf : r ∣ 2 * a + 1 := by
    rw [← hβ, ← hcardAut]
    exact orderOf_dvd_natCard β
  have hr2 : r ≠ 2 := by
    rintro rfl
    omega
  obtain ⟨g, hg⟩ := CFSG.RankThree.PartOne.RF4.largeRee_fieldAut_coset_conj a hK hr β hβ _ hhr
    ⟨u, rfl⟩
  obtain ⟨b, hk, ψ, hbr, hψinj, hψfix, -⟩ := exists_reeGamma_fixSubfield_hom hK hr hr2 β hβ
  have hle : T.map ((MulAut.conj g)⁻¹).toMonoidHom ≤ ψ.range := by
    rintro _ ⟨t, ht, rfl⟩
    have h1 := hfix t ht
    rw [hg] at h1
    have h2 : ReeTag.F4.reeGammaFieldAut K a β ((MulAut.conj g)⁻¹ t) = (MulAut.conj g)⁻¹ t := by
      apply (MulAut.conj g).injective
      have h1' : (MulAut.conj g) (ReeTag.F4.reeGammaFieldAut K a β ((MulAut.conj g)⁻¹ t)) = t := h1
      rw [h1', MulAut.apply_inv_self]
    exact (hψfix _).1 h2
  have hTcard : Nat.card T ∣ Nat.card ψ.range := by
    have h1 : Nat.card (T.map ((MulAut.conj g)⁻¹).toMonoidHom) = Nat.card T :=
      Subgroup.card_map_of_injective ((MulAut.conj g)⁻¹).injective
    rw [← h1]
    exact Subgroup.card_dvd_of_le hle
  have hψcard : Nat.card ψ.range = Nat.card (ReeTag.F4.reeGamma (fixSubfield β) b) :=
    (Nat.card_congr (MonoidHom.ofInjective hψinj).toEquiv).symm
  have hΓ₀ := (CFSG.RankThree.LargeReeOrder.large_Ree_exact_native_order_and_prime_factor_exhaustion
    b (fixSubfield β) hk).1
  have hSz := suzuki_order (a := a) hK
  have hTSz : Nat.card T = Nat.card (suzukiGroup a K) := Nat.card_congr eT.toEquiv
  have hQ : 2 ^ (2 * a + 1) = (2 ^ (2 * b + 1)) ^ r := by
    rw [← pow_mul, ← hbr]
  refine false_of_orders hr hr2 hr5 (b := b) ?_
  have hdvd : Nat.card T ∣ Nat.card (ReeTag.F4.reeGamma (fixSubfield β) b) := hψcard ▸ hTcard
  rw [hTSz, hSz, hΓ₀, hQ] at hdvd
  exact hdvd

end Outer

section Faithful

variable {K : Type} [Field K] [Finite K] [CharP K ReeTag.F4.prime] {a : ℕ}

theorem faithful_std (ha : 1 ≤ a) (hK : Nat.card K = 2 ^ (2 * a + 1)) (P : Plane5 K a)
    (g : MulAut (ReeTag.F4.reeGamma K a)) (hg : Nat.Coprime 5 (orderOf g))
    (hcomm : ∀ z, g * MulAut.conj (P.Ψ z) = MulAut.conj (P.Ψ z) * g)
    (hfix : ∀ z, z ≠ 1 → ∀ A Sg, IsDecomp P z A Sg → ∀ t ∈ Sg, g t = t) : g = 1 := by
  classical
  have hinj : Function.Injective
      (MulAut.conj : ReeTag.F4.reeGamma K a →* MulAut (ReeTag.F4.reeGamma K a)) :=
    CFSG.LieType.SeitzGeneration.conj_injective_of_center_eq_bot
      (ReeTag.large_Ree_fixed_group_center_trivial a K hK)
  by_contra hg1
  have hn1 : orderOf g ≠ 1 := fun h => hg1 (orderOf_eq_one_iff.1 h)
  have hnpos : 0 < orderOf g := orderOf_pos g
  have hr : (orderOf g).minFac.Prime := Nat.minFac_prime hn1
  have hrn : (orderOf g).minFac ∣ orderOf g := Nat.minFac_dvd _
  set r := (orderOf g).minFac with hrdef
  have hr5 : r ≠ 5 := by
    intro h5
    rw [h5] at hrn
    exact (Nat.not_coprime_of_dvd_of_dvd (by norm_num) (dvd_refl 5) hrn) hg
  set h := g ^ (orderOf g / r) with hhdef
  have hho : orderOf h = r := orderOf_pow_orderOf_div hnpos.ne' hrn
  have hhr : h ^ r = 1 := by
    rw [← hho]
    exact pow_orderOf_eq_one h
  have hhcomm : ∀ z, h * MulAut.conj (P.Ψ z) = MulAut.conj (P.Ψ z) * h := fun z =>
    ((Commute.pow_left (show Commute g (MulAut.conj (P.Ψ z)) from hcomm z) _).eq)
  have hhfix : ∀ z, z ≠ 1 → ∀ A Sg, IsDecomp P z A Sg → ∀ t ∈ Sg, h t = t := by
    intro z hz A Sg hd t ht
    have key : ∀ k : ℕ, (g ^ k) t = t := by
      intro k
      induction k with
      | zero => simp
      | succ k ih => rw [pow_succ, MulAut.mul_apply, hfix z hz A Sg hd t ht, ih]
    exact key _
  by_cases hin : h ∈ innerAut (ReeTag.F4.reeGamma K a)
  · obtain ⟨u, hu⟩ := hin
    have hu1 : u = 1 := by
      refine inner_eq_one ha hK P u (fun z => ?_) (fun z hz A Sg hd t ht => ?_)
      · apply hinj
        rw [map_mul, map_mul, hu]
        exact hhcomm z
      · have h1 := hhfix z hz A Sg hd t ht
        rw [← hu] at h1
        have h2 : u * t * u⁻¹ = t := by simpa [MulAut.conj_apply] using h1
        calc u * t = (u * t * u⁻¹) * u := by group
          _ = t * u := by rw [h2]
    have h1 : h = 1 := by rw [← hu, hu1, map_one]
    rw [h1, orderOf_one] at hho
    exact hr.one_lt.ne hho
  · obtain ⟨ξ, hξ⟩ := exists_primitive_five (AlgebraicClosure K)
    have hz₀ : planeElt hξ 1 0 ≠ 1 := planeElt_ne_one hξ (Or.inl (by decide))
    obtain ⟨A, Sg, hd⟩ := plane5_decomp hK P _ hz₀
    have hd' := hd
    obtain ⟨-, -, -, -, -, ⟨e⟩⟩ := hd'
    exact false_of_outer_prime_fix_suzuki ha hK Sg e hr hr5 hhr hin (hhfix _ hz₀ A Sg hd)

end Faithful

end CFSG.HardMathSupport.Dickson.LocalTwoBalance.Cross.W2.ReeF4FiveAux
