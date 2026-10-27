module

public import CFSG.GH74.Filter.Lie.SepWitness
public import CFSG.LieType.Chevalley.TwistRank

public section

namespace CFSG.LocalAnalysis.GLTheoremA.I107X2

open CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.LieType.BorelTits CFSG.Open
  CFSG.SectionRank CFSG.GH74.Filter.Lie


section Generic

variable {K : Type} [Field K] [CharP K 2]

@[expose] def paramTwist (σ : K →+* K) {k : ℕ} (π : Equiv.Perm (Fin k)) :
    (Fin k → Multiplicative K) →* (Fin k → Multiplicative K) where
  toFun x j := Multiplicative.ofAdd (σ (Multiplicative.toAdd (x (π.symm j))))
  map_one' := by
    funext j
    simp
  map_mul' x y := by
    funext j
    simp only [Pi.mul_apply, toAdd_mul, map_add, ofAdd_add]

theorem paramTwist_mulSingle (σ : K →+* K) {k : ℕ} (π : Equiv.Perm (Fin k)) [DecidableEq (Fin k)]
    (i : Fin k) (c : Multiplicative K) :
    paramTwist σ π (Pi.mulSingle i c) = Pi.mulSingle (π i) (Multiplicative.ofAdd (σ (Multiplicative.toAdd c))) := by
  funext j
  by_cases h : j = π i
  · subst h
    simp [paramTwist, Pi.mulSingle_apply]
  · have h' : π.symm j ≠ i := fun e => h (by rw [← e, Equiv.apply_symm_apply])
    simp [paramTwist, Pi.mulSingle_apply, h, h']

theorem twistC_rootHom {t : TwistTag} (σ : K →+* K) (α : Root t.tag) (c : Multiplicative K) :
    twistC t K σ (rootHom α c) =
      rootHom (rootTwist t α) (Multiplicative.ofAdd (σ (Multiplicative.toAdd c))) := by
  obtain ⟨ε, hε, h⟩ := (rootOperatorFamily t.tag).exists_twistC_eltElement t K σ α
  have hε1 : (ε : K) = 1 := by
    rcases hε with rfl | rfl
    · simp
    · push_cast
      exact CharTwo.neg_eq 1
  change twistC t K σ ((rootOperatorFamily t.tag).eltElement α (Multiplicative.toAdd c)) =
    (rootOperatorFamily t.tag).eltElement (rootTwist t α)
      (Multiplicative.toAdd (Multiplicative.ofAdd (σ (Multiplicative.toAdd c))))
  rw [h, hε1, one_mul]
  rfl

theorem hom_ext_mulSingle {ι : Type} [Fintype ι] [DecidableEq ι] {N : Type*} [Monoid N]
    (g h : (ι → Multiplicative K) →* N)
    (H : ∀ (i : ι) (c : Multiplicative K), g (Pi.mulSingle i c) = h (Pi.mulSingle i c)) : g = h := by
  ext x
  let m : ι → ι → Multiplicative K := fun i => Pi.mulSingle (M := fun _ => Multiplicative K) i (x i)
  have hcomm : ∀ i ∈ (Finset.univ : Finset ι), ∀ j ∈ (Finset.univ : Finset ι),
      Commute (m i) (m j) := fun _ _ _ _ => Commute.all _ _
  have e1 : (Finset.univ : Finset ι).noncommProd m (fun _ hi _ hj _ => hcomm _ hi _ hj) = x := by
    rw [Finset.noncommProd_eq_prod]
    exact Finset.univ_prod_mulSingle x
  calc g x = g ((Finset.univ : Finset ι).noncommProd m (fun _ hi _ hj _ => hcomm _ hi _ hj)) := by
        rw [e1]
    _ = (Finset.univ : Finset ι).noncommProd (fun i => g (m i))
        (fun _ hi _ hj _ => (hcomm _ hi _ hj).map g) := Finset.map_noncommProd _ _ _ _
    _ = (Finset.univ : Finset ι).noncommProd (fun i => h (m i))
        (fun _ hi _ hj _ => (hcomm _ hi _ hj).map h) :=
          Finset.noncommProd_congr rfl (fun i _ => H i (x i)) _
    _ = h ((Finset.univ : Finset ι).noncommProd m (fun _ hi _ hj _ => hcomm _ hi _ hj)) :=
          (Finset.map_noncommProd _ _ _ _).symm
    _ = h x := by rw [e1]

theorem exists_subgroup_card_two_pow {G : Type*} [Group G] [Finite G] {N j : ℕ}
    (hdvd : Nat.card G ∣ 2 ^ N) (hle : 2 ^ j ≤ Nat.card G) :
    ∃ B : Subgroup G, Nat.card B = 2 ^ j := by
  obtain ⟨s, -, hG⟩ := (Nat.dvd_prime_pow Nat.prime_two).1 hdvd
  have hjs : j ≤ s := by
    rw [hG] at hle
    exact (Nat.pow_le_pow_iff_right (by norm_num)).1 hle
  obtain ⟨B, hB, -⟩ := Sylow.exists_subgroup_card_pow_prime_le 2 (n := 0) (m := j)
    (by rw [hG]; exact Nat.pow_dvd_pow 2 hjs) ⊥ (by simp) (Nat.zero_le _)
  exact ⟨B, hB⟩

theorem sq_eq_one_of_charTwo {k : ℕ} (x : Fin k → Multiplicative K) : x ^ 2 = 1 := by
  funext i
  change (x i) ^ 2 = 1
  apply Multiplicative.toAdd.injective
  rw [toAdd_pow, toAdd_one, two_nsmul, ← two_nsmul]
  simp only [two_nsmul]
  rw [← two_mul]
  have h2 : (2 : K) = 0 := by
    have := CharP.cast_eq_zero K 2
    simpa using this
  rw [h2, zero_mul]

end Generic

section Main

variable {t : TwistTag} {K : Type} [Field K] [Finite K] [CharP K 2]

theorem le_pRank_of_twistedWitness (σ : K →+* K)
    (hU : ∀ x ∈ (nativeData t.tag K).U, twistC t K σ x = x → x ∈ twistDerived t K σ)
    {k : ℕ} (W : SepWitness t.tag k) (hW : W.check = true) (π : Equiv.Perm (Fin k))
    (hπ : ∀ i, rootTwist t (W.root i) = W.root (π i))
    (B : Subgroup (Fin k → Multiplicative K))
    (hB : B ≤ MonoidHom.eqLocus (paramTwist σ π) (MonoidHom.id _)) {j : ℕ}
    (hj : Nat.card B = 2 ^ j) :
    j ≤ CFSG.Open.pRank 2 (⊤ : Subgroup (commutator (twistFixed t K σ))) := by
  classical
  obtain ⟨hcomm, hinj⟩ := SepWitness.pi_data hW (K := K)
  set Φ := MonoidHom.noncommPiCoprod (fun i => rootHom (K := K) (W.root i)) hcomm with hΦ
  have hFΦ : (twistC t K σ).comp Φ = Φ.comp (paramTwist σ π) := by
    apply hom_ext_mulSingle
    intro i c
    simp only [MonoidHom.comp_apply, hΦ, MonoidHom.noncommPiCoprod_mulSingle]
    rw [twistC_rootHom, hπ i, paramTwist_mulSingle, MonoidHom.noncommPiCoprod_mulSingle]
  have hpos : ∀ i, 0 < height (W.root i).1 := fun i => SepWitness.root_pos hW i
  have hUroot : ∀ i (c : Multiplicative K), rootHom (K := K) (W.root i) c ∈ (nativeData t.tag K).U :=
    fun i c => RootGroupData.X_le_U (D := nativeData t.tag K) (hpos i)
      ((rootOperatorFamily t.tag).eltElement_mem_rootSubgroup _ _)
  have hUΦ : ∀ a : Fin k → Multiplicative K, Φ a ∈ (nativeData t.tag K).U := fun a => by
    have e : Φ a = Finset.univ.noncommProd (fun i => rootHom (K := K) (W.root i) (a i))
        (fun _ _ _ _ h => hcomm h _ _) := rfl
    rw [e]
    exact Subgroup.noncommProd_mem _ (fun _ _ _ _ h => hcomm h _ _) (fun i _ => hUroot i (a i))
  let Ψ : B →* adjointGroup t.tag K := Φ.comp B.subtype
  have hΨinj : Function.Injective Ψ := hinj.comp Subtype.val_injective
  have hΨrange : Ψ.range ≤ twistDerived t K σ := by
    rintro _ ⟨b, rfl⟩
    have hb : paramTwist σ π b.1 = b.1 := hB b.2
    apply hU _ (hUΦ b.1)
    change twistC t K σ (Φ b.1) = Φ b.1
    have h1 : (twistC t K σ).comp Φ b.1 = Φ.comp (paramTwist σ π) b.1 := by rw [hFΦ]
    rw [MonoidHom.comp_apply, MonoidHom.comp_apply, hb] at h1
    exact h1
  have hcomm' : ∀ a b : B, a * b = b * a := fun a b => by
    apply Subtype.ext
    exact mul_comm (a : Fin k → Multiplicative K) (b : Fin k → Multiplicative K) |>.trans rfl
  have hpow' : ∀ a : B, a ^ 2 = 1 := fun a => by
    apply Subtype.ext
    exact sq_eq_one_of_charTwo (a : Fin k → Multiplicative K)
  exact le_pRank_of_commutator (Ψ := Ψ) hΨinj hΨrange (p := 2) (fun a b => hcomm' a b)
    (fun a => hpow' a) hj

end Main

end CFSG.LocalAnalysis.GLTheoremA.I107X2

end
