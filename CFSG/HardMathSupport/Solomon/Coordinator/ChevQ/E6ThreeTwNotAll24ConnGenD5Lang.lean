module

public import CFSG.HardMathSupport.Solomon.Coordinator.ChevQ.E6ThreeTwNotAll24ConnGenD5Abs
public import CFSG.HardMathSupport.Solomon.Coordinator.ChevQ.E6ThreeTwNotAll24ConnGenD5Pos
public import CFSG.HardMathSupport.Lang.TwE6Step3.TwoA2Split

public section

namespace CFSG.HardMathSupport.Solomon.Coordinator.ChevQ.E6Three

namespace KSGen

open CFSG.Open CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley
  CFSG.HardMathSupport.Timmesfeld.LangTorus CFSG.HardMathSupport.Timmesfeld.CrossChar
  CFSG.LocalAnalysis.ComponentInitial CFSG.LocalAnalysis.ComponentInitial.FourGroupChevalley
  CFSG.LieType.AlgebraicGroups CFSG.RankThree.PartOne.KE
  CFSG.HardMathSupport.Solomon.Coordinator.LieSemisimple
  CFSG.HardMathSupport.Solomon.Coordinator.ChevQ.E6Three.KSConn
  CFSG.HardMathSupport.Lang CFSG.HardMathSupport.Lang.TwE6Step3

set_option linter.unusedSectionVars false


section Abstract

theorem exists_inv_mul_apply_eq {G : Type*} [CommGroup G]
    (hdiv : ∀ (g : G) (n : ℕ), 0 < n → ∃ h : G, h ^ n = g) (f : G →* G) (m Q : ℕ)
    (hQ : 2 ≤ Q) (hf : ∀ g, f^[m] g = g ^ Q) (s : G) : ∃ t : G, t⁻¹ * f t = s := by
  obtain ⟨u, hu⟩ := hdiv s (Q - 1) (by omega)
  have key : ∀ k : ℕ, (∏ i ∈ Finset.range k, f^[i] u)⁻¹ * f (∏ i ∈ Finset.range k, f^[i] u) =
      u⁻¹ * f^[k] u := by
    intro k
    induction k with
    | zero => simp
    | succ k ih =>
      rw [Finset.prod_range_succ, map_mul, mul_inv, Function.iterate_succ_apply']
      calc (∏ i ∈ Finset.range k, f^[i] u)⁻¹ * (f^[k] u)⁻¹ *
            (f (∏ i ∈ Finset.range k, f^[i] u) * f (f^[k] u))
          = ((∏ i ∈ Finset.range k, f^[i] u)⁻¹ * f (∏ i ∈ Finset.range k, f^[i] u)) *
              ((f^[k] u)⁻¹ * f (f^[k] u)) := mul_mul_mul_comm _ _ _ _
        _ = u⁻¹ * f^[k] u * ((f^[k] u)⁻¹ * f (f^[k] u)) := by rw [ih]
        _ = u⁻¹ * f (f^[k] u) := by
          rw [mul_assoc, ← mul_assoc (f^[k] u), mul_inv_cancel, one_mul]
  refine ⟨∏ i ∈ Finset.range m, f^[i] u, ?_⟩
  rw [key, hf, ← hu]
  have hQ' : Q = (Q - 1) + 1 := by omega
  rw [hQ', pow_succ]
  simp [mul_comm]

theorem exists_inv_mul_apply_eq_of_subgroup {M : Type*} [Group M] (T : Subgroup M)
    (hcomm : ∀ x ∈ T, ∀ y ∈ T, x * y = y * x)
    (hdiv : ∀ g ∈ T, ∀ n : ℕ, 0 < n → ∃ h ∈ T, h ^ n = g)
    (f : M →* M) (hfT : ∀ x ∈ T, f x ∈ T) (m Q : ℕ) (hQ : 2 ≤ Q)
    (hf : ∀ g ∈ T, f^[m] g = g ^ Q) :
    ∀ s ∈ T, ∃ t ∈ T, t⁻¹ * f t = s := by
  intro s hs
  letI : CommGroup T :=
    { (inferInstance : Group T) with mul_comm := fun x y => Subtype.ext (hcomm _ x.2 _ y.2) }
  let f' : T →* T :=
    { toFun := fun x => ⟨f x, hfT x x.2⟩
      map_one' := Subtype.ext (map_one f)
      map_mul' := fun x y => Subtype.ext (map_mul f (x : M) (y : M)) }
  have hit : ∀ (k : ℕ) (x : T), ((f'^[k] x : T) : M) = f^[k] (x : M) := by
    intro k
    induction k with
    | zero => intro x; rfl
    | succ k ih =>
      intro x
      rw [Function.iterate_succ_apply, Function.iterate_succ_apply]
      exact ih ⟨f x, hfT x x.2⟩
  obtain ⟨t, ht⟩ := exists_inv_mul_apply_eq (G := T)
    (fun g n hn => by
      obtain ⟨h, hh, hhn⟩ := hdiv g g.2 n hn
      exact ⟨⟨h, hh⟩, Subtype.ext hhn⟩)
    f' m Q hQ (fun g => Subtype.ext (by rw [hit]; exact hf g g.2)) ⟨s, hs⟩
  exact ⟨t, t.2, congrArg Subtype.val ht⟩

end Abstract

section Lattice

variable {L : Type} [Field L]

@[expose] noncomputable def thetaLat (w : WeylGroup Tag.E6) (v : Fin Tag.E6.rank → ℤ) :
    Fin Tag.E6.rank → ℤ :=
  permLattice e6Graph.symm (w⁻¹ • v)

theorem thetaLat_injective (w : WeylGroup Tag.E6) : Function.Injective (thetaLat w) := by
  intro x y h
  exact MulAction.injective w⁻¹ (permLattice_injective (τ := Tag.E6) _ h)

theorem isRoot_thetaLat (w : WeylGroup Tag.E6) {γ : Fin Tag.E6.rank → ℤ}
    (hγ : IsRoot Tag.E6 γ) : IsRoot Tag.E6 (thetaLat w γ) :=
  (CFSG.LieType.Chevalley.IsRoot.smul hγ w⁻¹).permLattice
    (cartan_perm_symm e6Graph_cartan)

theorem exists_iterate_thetaLat_eq (w : WeylGroup Tag.E6) :
    ∃ m : ℕ, 1 ≤ m ∧ ∀ i : Fin Tag.E6.rank,
      (thetaLat w)^[m] (Pi.single i 1) = Pi.single i 1 := by
  obtain ⟨d, hd, hdfix⟩ := exists_iterate_eq_of_mapsTo
    (CFSG.Blueprint.Chevalley.finite_setOf_isRoot Tag.E6)
    (fun γ hγ => isRoot_thetaLat w hγ) (thetaLat_injective w).injOn
  exact ⟨d, hd, fun i => hdfix _ (IsRoot.basis i)⟩

@[expose] noncomputable def stepTuple (w : WeylGroup Tag.E6) (Fr : L →+* L)
    (b : Fin Tag.E6.rank → Lˣ) : Fin Tag.E6.rank → Lˣ :=
  weylTuple w (fun i => Units.map Fr.toMonoidHom (b (e6Graph.symm i)))

theorem rootChar_stepTuple {Fr : L →+* L} {q : ℕ} (hFr : ∀ c, Fr c = c ^ q)
    (w : WeylGroup Tag.E6) (b : Fin Tag.E6.rank → Lˣ) (u : Fin Tag.E6.rank → ℤ) :
    rootChar (stepTuple w Fr b) u = rootChar b (thetaLat w u) ^ q := by
  rw [stepTuple, rootChar_weylTuple, rootChar_map_tuple, thetaLat, rootChar_permLattice]
  exact Units.ext (by simp [hFr])

theorem rootChar_iterate_stepTuple {Fr : L →+* L} {q : ℕ} (hFr : ∀ c, Fr c = c ^ q)
    (w : WeylGroup Tag.E6) (k : ℕ) (b : Fin Tag.E6.rank → Lˣ) (u : Fin Tag.E6.rank → ℤ) :
    rootChar ((stepTuple w Fr)^[k] b) u = rootChar b ((thetaLat w)^[k] u) ^ (q ^ k) := by
  induction k generalizing b u with
  | zero => simp
  | succ k ih =>
    rw [Function.iterate_succ_apply, ih, rootChar_stepTuple hFr, ← pow_mul, ← pow_succ',
      Function.iterate_succ_apply' (thetaLat w)]

theorem stepTuple_iterate_eq_pow {Fr : L →+* L} {q : ℕ} (hFr : ∀ c, Fr c = c ^ q)
    (w : WeylGroup Tag.E6) {m : ℕ}
    (hm : ∀ i : Fin Tag.E6.rank, (thetaLat w)^[m] (Pi.single i 1) = Pi.single i 1)
    (b : Fin Tag.E6.rank → Lˣ) : (stepTuple w Fr)^[m] b = b ^ (q ^ m) := by
  funext i
  have h1 := rootChar_iterate_stepTuple hFr w m b (Pi.single i 1)
  rw [hm i, CFSG.RankThree.PartOne.KE.CTTorus.rootChar_single,
    CFSG.RankThree.PartOne.KE.CTTorus.rootChar_single] at h1
  exact h1

theorem step_iterate_rootDiagUnit {Fr : L →+* L} {w : WeylGroup Tag.E6}
    {f : ModGL Tag.E6 L →* ModGL Tag.E6 L}
    (hf : f = twFrob TwistTag.E6 (canonicalRep (coxeterSystem TwistTag.E6.tag) L w) Fr)
    (k : ℕ) (b : Fin Tag.E6.rank → Lˣ) :
    f^[k] (rootDiagUnit Tag.E6 b) = rootDiagUnit Tag.E6 ((stepTuple w Fr)^[k] b) := by
  induction k generalizing b with
  | zero => rfl
  | succ k ih =>
    have h1 : f (rootDiagUnit Tag.E6 b) = rootDiagUnit Tag.E6 (stepTuple w Fr b) := by
      rw [hf]
      exact twFrob_rootDiagUnit TwistTag.E6 Fr w b
    rw [Function.iterate_succ_apply, Function.iterate_succ_apply, h1, ih]

end Lattice

section Torus

variable {L : Type} [Field L] [IsAlgClosed L]

theorem exists_unit_pow_eq (n : ℕ) (hn : 0 < n) (x : Lˣ) : ∃ y : Lˣ, y ^ n = x := by
  obtain ⟨y, hy⟩ := IsAlgClosed.exists_pow_nat_eq (x : L) hn
  have hy0 : y ≠ 0 := by
    rintro rfl
    rw [zero_pow hn.ne'] at hy
    exact x.ne_zero hy.symm
  exact ⟨Units.mk0 y hy0, Units.ext (by simpa using hy)⟩

theorem torus_inf_rootSpan_divisible (v : WeylGroup Tag.E6) (J : Set (Fin Tag.E6.rank))
    {g : ModGL Tag.E6 L}
    (hg : g ∈ torusGroup Tag.E6 L ⊓
      rootSpan Tag.E6 L ((fun α => v • α) '' parabolicRoots Tag.E6 J)) (n : ℕ) (hn : 0 < n) :
    ∃ h ∈ torusGroup Tag.E6 L ⊓
      rootSpan Tag.E6 L ((fun α => v • α) '' parabolicRoots Tag.E6 J), h ^ n = g := by
  classical
  obtain ⟨hgH, hgQ⟩ := Subgroup.mem_inf.1 hg
  have hg' : (canonicalRep (coxeterSystem Tag.E6) L v)⁻¹ * g *
      canonicalRep (coxeterSystem Tag.E6) L v ∈ supportedTorus Tag.E6 L J := by
    rw [← torusGroup_inf_rootSpan_parabolicRoots]
    refine Subgroup.mem_inf.2 ⟨TwE6Step3.canonicalRep_inv_conj_mem_torusGroup v hgH, ?_⟩
    refine TwE6Step3.canonicalRep_inv_conj_mem_rootSpan v (fun γ hγ => ?_) hgQ
    obtain ⟨α, hα, rfl⟩ := hγ
    exact ⟨CFSG.LieType.Chevalley.IsRoot.smul hα.1 v, by rwa [inv_smul_smul]⟩
  obtain ⟨b, hb⟩ := mem_supportedTorus.1 hg'
  choose c hc using exists_unit_pow_eq (L := L) n hn
  have hbc : (fun j => c (b j)) ^ n = b := funext fun j => hc (b j)
  have hmem : supportedTorusHom Tag.E6 L J (fun j => c (b j)) ∈
      torusGroup Tag.E6 L ⊓ rootSpan Tag.E6 L (parabolicRoots Tag.E6 J) := by
    rw [torusGroup_inf_rootSpan_parabolicRoots]
    exact supportedTorusHom_mem J _
  obtain ⟨hmH, hmQ⟩ := Subgroup.mem_inf.1 hmem
  refine ⟨canonicalRep (coxeterSystem Tag.E6) L v *
    supportedTorusHom Tag.E6 L J (fun j => c (b j)) *
      (canonicalRep (coxeterSystem Tag.E6) L v)⁻¹, Subgroup.mem_inf.2 ⟨?_, ?_⟩, ?_⟩
  · exact (Subgroup.mem_normalizer_iff.1 (canonicalRep_mem_normalizer v) _).1 hmH
  · exact TwE6Step3.canonicalRep_conj_mem_rootSpan v
      (S' := (fun α => v • α) '' parabolicRoots Tag.E6 J)
      (fun γ hγ => ⟨hγ.1, ⟨γ, hγ, rfl⟩⟩) hmQ
  · rw [conj_pow, ← map_pow, hbc, hb]
    group

end Torus

theorem d5TorusLang : D5TorusLang := by
  classical
  intro L _ _ p₀ S Fr hFr hΦ h3 h3q hq2 a hT hap hk s hs
  obtain ⟨v, J, -, hker⟩ := d5_position h3 hap hk
  obtain ⟨r, e, hr, hchar, he, hq⟩ := S.exists_char_pow
  haveI : Fact r.Prime := ⟨hr⟩
  haveI := hchar
  obtain ⟨w, hn⟩ := S.D.n_weyl
  have hst : S.D.step = twFrob TwistTag.E6
      (canonicalRep (coxeterSystem TwistTag.E6.tag) L w) Fr := by
    ext1 g
    change S.D.n * S.D.Φ g * S.D.n⁻¹ = canonicalRep (coxeterSystem TwistTag.E6.tag) L w *
      twistHom TwistTag.E6 L Fr g * (canonicalRep (coxeterSystem TwistTag.E6.tag) L w)⁻¹
    rw [hΦ, hn]
    rfl
  obtain ⟨m, hm, hΘ⟩ := exists_iterate_thetaLat_eq w
  have hq2' : 2 ≤ S.D.q := by
    rw [hq]
    exact hr.two_le.trans (Nat.le_self_pow (by omega) r)
  have hQ : 2 ≤ S.D.q ^ m := hq2'.trans (Nat.le_self_pow (by omega) _)
  have hpow : ∀ g ∈ torusGroup Tag.E6 L, S.D.step^[m] g = g ^ (S.D.q ^ m) := by
    intro g hg
    obtain ⟨b, rfl⟩ := exists_rootDiagUnit_eq_of_mem_torusGroup hg
    rw [step_iterate_rootDiagUnit hst m b, stepTuple_iterate_eq_pow hFr w hΘ b,
      rootDiagUnit_pow]
  exact exists_inv_mul_apply_eq_of_subgroup
    (torusGroup Tag.E6 L ⊓ rootSpan Tag.E6 L (kernelRoots (rootCharHom a)))
    (fun x hx y hy => torusGroup_comm (Subgroup.mem_inf.1 hx).1 (Subgroup.mem_inf.1 hy).1)
    (fun g hg n hn => by
      rw [hker] at hg ⊢
      exact torus_inf_rootSpan_divisible v J hg n hn)
    S.D.step
    (fun x hx => Subgroup.mem_inf.2 ⟨step_mem_torusGroup S hq (Subgroup.mem_inf.1 hx).1,
      step_mem_rootSpan S (fun γ hγ => hγ.1)
        (fun γ hγ => rho_mem_kernelRoots_of_mem_torus S hT γ hγ) (Subgroup.mem_inf.1 hx).2⟩)
    m (S.D.q ^ m) hQ (fun g hg => hpow g (Subgroup.mem_inf.1 hg).1) s hs

end KSGen

end CFSG.HardMathSupport.Solomon.Coordinator.ChevQ.E6Three
