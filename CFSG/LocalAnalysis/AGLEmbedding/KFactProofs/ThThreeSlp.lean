module

public import CFSG.LocalAnalysis.AGLEmbedding.KFactProofs.ThThreeDefs
public import CFSG.LocalAnalysis.AGLEmbedding.KFactProofs.ThThreeEquiv
public import CFSG.RankThree.Asc83Table.MatCert
public import CFSG.Sporadic.Th.Max3.Maximal
public import CFSG.LocalAnalysis.SectionRank.Sporadic.OpsF2

public section

namespace CFSG.AGLEmbedding.R3

open CFSG.RankThree.Asc83Table CFSG.RankThree.Asc83Table.Native CFSG.SectionRank
  CFSG.SectionRank.Native CFSG.Blueprint CFSG.Sporadic.Th CFSG.SectionRank.LocalWitness

theorem orderOf_a :
    orderOf (a : J) = 2 := by
  rw [← Max3.z_eq_a]
  exact orderOf_eq_prime (by rw [sq]; exact Max3.z_mul_self) Max3.z_ne_one

theorem centralizer_eq_closure
    {t x y : NativeSporadic.Th} (ht : thEquivJ t = a)
    (hx : thEquivJ x = Max3.x) (hy : thEquivJ y = Max3.y) :
    Subgroup.centralizer ({t} : Set NativeSporadic.Th) = Subgroup.closure {x, y} := by
  have hCa := Kernel.centralizer_a_eq_M th_kernel_facts
  have h1 : Subgroup.centralizer ({t} : Set NativeSporadic.Th) =
      (Subgroup.centralizer ({a} : Set J)).comap (thEquivJ : NativeSporadic.Th →* J) := by
    ext u
    simp only [Subgroup.mem_comap, Subgroup.mem_centralizer_singleton_iff, MonoidHom.coe_ofClass]
    rw [← ht, ← map_mul, ← map_mul, thEquivJ.injective.eq_iff]
  rw [h1, hCa]
  have hxs : thEquivJ.symm Max3.x = x := by rw [← hx]; simp
  have hys : thEquivJ.symm Max3.y = y := by rw [← hy]; simp
  show Subgroup.comap (thEquivJ : NativeSporadic.Th →* J) (Subgroup.closure {Max3.x, Max3.y}) = _
  rw [Subgroup.comap_equiv_eq_map_symm, MonoidHom.map_closure]
  simp only [Set.image_insert_eq, Set.image_singleton]
  simp [hxs, hys]

theorem conj_mem_closure_of {G : Type*} [Group G] (S : Set G) (g : G) {T : Set G}
    (hT : ∀ w ∈ T, g * w * g⁻¹ ∈ Subgroup.closure S) :
    ∀ w ∈ Subgroup.closure T, g * w * g⁻¹ ∈ Subgroup.closure S := by
  intro w hw
  induction hw using Subgroup.closure_induction with
  | mem w hw => exact hT w hw
  | one => simp
  | mul a b _ _ ha hb =>
    have : g * (a * b) * g⁻¹ = (g * a * g⁻¹) * (g * b * g⁻¹) := by group
    rw [this]
    exact Subgroup.mul_mem _ ha hb
  | inv a _ ha =>
    have : g * a⁻¹ * g⁻¹ = (g * a * g⁻¹)⁻¹ := by group
    rw [this]
    exact Subgroup.inv_mem _ ha

theorem closure_eq_top_of_centralizers {G : Type*} [Group G] {S : Set G} {t x y g : G}
    (hC1 : Subgroup.centralizer ({t} : Set G) = Subgroup.closure {x, y})
    (hsup : Subgroup.centralizer ({t} : Set G) ⊔ Subgroup.centralizer ({g * t * g⁻¹} : Set G) = ⊤)
    (hxS : x ∈ Subgroup.closure S) (hyS : y ∈ Subgroup.closure S)
    (hxS' : g * x * g⁻¹ ∈ Subgroup.closure S) (hyS' : g * y * g⁻¹ ∈ Subgroup.closure S) :
    Subgroup.closure S = ⊤ := by
  have hle1 : Subgroup.centralizer ({t} : Set G) ≤ Subgroup.closure S := by
    rw [hC1, Subgroup.closure_le]
    rintro w (rfl | rfl)
    · exact hxS
    · exact hyS
  have hle2 : Subgroup.centralizer ({g * t * g⁻¹} : Set G) ≤ Subgroup.closure S := by
    intro z hz
    have hz' : g⁻¹ * z * g ∈ Subgroup.centralizer ({t} : Set G) := by
      rw [Subgroup.mem_centralizer_singleton_iff] at hz ⊢
      calc g⁻¹ * z * g * t = g⁻¹ * (z * (g * t * g⁻¹)) * g := by group
        _ = g⁻¹ * ((g * t * g⁻¹) * z) * g := by rw [hz]
        _ = t * (g⁻¹ * z * g) := by group
    rw [hC1] at hz'
    have e : z = g * (g⁻¹ * z * g) * g⁻¹ := by group
    rw [e]
    refine conj_mem_closure_of S g (T := {x, y}) ?_ _ hz'
    rintro w (rfl | rfl)
    · exact hxS'
    · exact hyS'
  rw [eq_top_iff, ← hsup]
  exact sup_le hle1 hle2

theorem th_closure_eq_top
    {S : Set NativeSporadic.Th} {t x y g : NativeSporadic.Th}
    (ht : thEquivJ t = a) (hx : thEquivJ x = Max3.x) (hy : thEquivJ y = Max3.y)
    (hne : g * t * g⁻¹ ≠ t)
    (hxS : x ∈ Subgroup.closure S) (hyS : y ∈ Subgroup.closure S)
    (hxS' : g * x * g⁻¹ ∈ Subgroup.closure S) (hyS' : g * y * g⁻¹ ∈ Subgroup.closure S) :
    Subgroup.closure S = ⊤ := by
  have h2 : orderOf t = 2 := by
    have h := orderOf_a
    rw [← ht, MulEquiv.orderOf_eq] at h
    exact h
  have h2' : orderOf (g * t * g⁻¹) = 2 :=
    (orderOf_eq_of_isConj (isConj_iff.2 ⟨g, rfl⟩ : IsConj t (g * t * g⁻¹))).symm.trans h2
  exact closure_eq_top_of_centralizers (centralizer_eq_closure ht hx hy)
    (th_sup_centralizer_eq_top t (g * t * g⁻¹) h2 h2' hne.symm) hxS hyS hxS' hyS'


theorem hasOrd_of_slp {C : MCert} (hf : ∀ f ∈ thSlpFacts, f ∈ C.facts) {w : Word}
    (h : w.all (fun q => thSlpFacts.any fun f => match f with
      | .ord r _ => r == q.1
      | _ => false) = true) : HasOrd C w :=
  hasOrd_of_bool (by
    simp only [List.all_eq_true] at h ⊢
    intro q hq
    obtain ⟨f, hfm, hfq⟩ := List.any_eq_true.1 (h q hq)
    exact List.any_eq_true.2 ⟨f, hf f hfm, hfq⟩)

section
variable {C : MCert}
  (hC : mcertCheck (ops2 248) NativeSporadic.ThSeed1 NativeSporadic.ThSeed2 C = true)
  (hf : ∀ f ∈ thSlpFacts, f ∈ C.facts)
  (hA : (ops2 248).eq (certRegs (ops2 248) NativeSporadic.ThSeed1 NativeSporadic.ThSeed2 C)[0]!
    ((ops2 248).decode NativeSporadic.ThSeed1) = true)
  (hB : (ops2 248).eq (certRegs (ops2 248) NativeSporadic.ThSeed1 NativeSporadic.ThSeed2 C)[1]!
    ((ops2 248).decode NativeSporadic.ThSeed2) = true)

include hf hA hB in
theorem thSlp_ident :
    thEquivJ (regUnit (spec2 248) hC 0) = a ∧ thEquivJ (regUnit (spec2 248) hC 1) = b ∧
      thEquivJ (regUnit (spec2 248) hC 17) = Max3.x ∧
      thEquivJ (regUnit (spec2 248) hC 19) = Max3.y := by
  have key : ∀ (w₁ w₂ : Word), MFact.eq w₁ w₂ ∈ thSlpFacts →
      w₁.all (fun q => thSlpFacts.any fun f => match f with
        | .ord r _ => r == q.1
        | _ => false) = true →
      w₂.all (fun q => thSlpFacts.any fun f => match f with
        | .ord r _ => r == q.1
        | _ => false) = true →
      wordUnit (spec2 248) hC w₁ = wordUnit (spec2 248) hC w₂ :=
    fun w₁ w₂ hm h₁ h₂ => regUnit_eq (spec2 248) hC (hf _ hm) (hasOrd_of_slp hf h₁)
      (hasOrd_of_slp hf h₂)
  have fordA : MFact.ord 0 2 ∈ C.facts := hf _ (by simp [thSlpFacts])
  have fordB : MFact.ord 1 3 ∈ C.facts := hf _ (by simp [thSlpFacts])
  have hr0 := (reg_pow (spec2 248) hC fordA).1
  have hr1 := (reg_pow (spec2 248) hC fordB).1
  have hvalA : valHom (certMonoid 2 248 NativeSporadic.ThSeed1 NativeSporadic.ThSeed2)
      (regUnit (spec2 248) hC 0) = NativeSporadic.decode 2 248 1 NativeSporadic.ThSeed1 := by
    rw [val_regUnit (spec2 248) hC fordA, (spec2 248).toMat_eq (reg_ok (spec2 248) hC hr0).1
      ((spec2 248).decode_wf _) hA, (spec2 248).toMat_decode]
  have hvalB : valHom (certMonoid 2 248 NativeSporadic.ThSeed1 NativeSporadic.ThSeed2)
      (regUnit (spec2 248) hC 1) = NativeSporadic.decode 2 248 1 NativeSporadic.ThSeed2 := by
    rw [val_regUnit (spec2 248) hC fordB, (spec2 248).toMat_eq (reg_ok (spec2 248) hC hr1).1
      ((spec2 248).decode_wf _) hB, (spec2 248).toMat_decode]
  have e0 : thEquivJ (regUnit (spec2 248) hC 0) = a :=
    Subtype.ext (Units.ext ((thEquivJ_val _).trans (hvalA.trans (a_val).symm)))
  have e1 : thEquivJ (regUnit (spec2 248) hC 1) = b :=
    Subtype.ext (Units.ext ((thEquivJ_val _).trans (hvalB.trans (b_val).symm)))
  have h2 : regUnit (spec2 248) hC 2 = regUnit (spec2 248) hC 0 * regUnit (spec2 248) hC 1 := by
    simpa [wordUnit] using key [(2, 1)] [(0, 1), (1, 1)] (by simp [thSlpFacts]) (by decide)
      (by decide)
  have h3 : regUnit (spec2 248) hC 3 = regUnit (spec2 248) hC 2 * regUnit (spec2 248) hC 1 := by
    simpa [wordUnit] using key [(3, 1)] [(2, 1), (1, 1)] (by simp [thSlpFacts]) (by decide)
      (by decide)
  have h4 : regUnit (spec2 248) hC 4 = regUnit (spec2 248) hC 2 * regUnit (spec2 248) hC 3 := by
    simpa [wordUnit] using key [(4, 1)] [(2, 1), (3, 1)] (by simp [thSlpFacts]) (by decide)
      (by decide)
  have h5 : regUnit (spec2 248) hC 5 = regUnit (spec2 248) hC 2 * regUnit (spec2 248) hC 4 := by
    simpa [wordUnit] using key [(5, 1)] [(2, 1), (4, 1)] (by simp [thSlpFacts]) (by decide)
      (by decide)
  have h6 : regUnit (spec2 248) hC 6 = regUnit (spec2 248) hC 0 * regUnit (spec2 248) hC 5 := by
    simpa [wordUnit] using key [(6, 1)] [(0, 1), (5, 1)] (by simp [thSlpFacts]) (by decide)
      (by decide)
  have h7 : regUnit (spec2 248) hC 7 = regUnit (spec2 248) hC 5 * regUnit (spec2 248) hC 0 := by
    simpa [wordUnit] using key [(7, 1)] [(5, 1), (0, 1)] (by simp [thSlpFacts]) (by decide)
      (by decide)
  have h9 : regUnit (spec2 248) hC 9 = regUnit (spec2 248) hC 8 * regUnit (spec2 248) hC 6 := by
    simpa [wordUnit] using key [(9, 1)] [(8, 1), (6, 1)] (by simp [thSlpFacts]) (by decide)
      (by decide)
  have h10 : regUnit (spec2 248) hC 10 = regUnit (spec2 248) hC 5 * regUnit (spec2 248) hC 4 := by
    simpa [wordUnit] using key [(10, 1)] [(5, 1), (4, 1)] (by simp [thSlpFacts]) (by decide)
      (by decide)
  have h11 : regUnit (spec2 248) hC 11 = regUnit (spec2 248) hC 2 * regUnit (spec2 248) hC 10 := by
    simpa [wordUnit] using key [(11, 1)] [(2, 1), (10, 1)] (by simp [thSlpFacts]) (by decide)
      (by decide)
  have h12 : regUnit (spec2 248) hC 12 = regUnit (spec2 248) hC 11 * regUnit (spec2 248) hC 3 := by
    simpa [wordUnit] using key [(12, 1)] [(11, 1), (3, 1)] (by simp [thSlpFacts]) (by decide)
      (by decide)
  have h13 : regUnit (spec2 248) hC 13 = regUnit (spec2 248) hC 0 * regUnit (spec2 248) hC 12 := by
    simpa [wordUnit] using key [(13, 1)] [(0, 1), (12, 1)] (by simp [thSlpFacts]) (by decide)
      (by decide)
  have h14 : regUnit (spec2 248) hC 14 = regUnit (spec2 248) hC 12 * regUnit (spec2 248) hC 0 := by
    simpa [wordUnit] using key [(14, 1)] [(12, 1), (0, 1)] (by simp [thSlpFacts]) (by decide)
      (by decide)
  have h16 : regUnit (spec2 248) hC 16 = regUnit (spec2 248) hC 15 * regUnit (spec2 248) hC 13 := by
    simpa [wordUnit] using key [(16, 1)] [(15, 1), (13, 1)] (by simp [thSlpFacts]) (by decide)
      (by decide)
  have h19 : regUnit (spec2 248) hC 19 = regUnit (spec2 248) hC 6 * regUnit (spec2 248) hC 18 := by
    simpa [wordUnit] using key [(19, 1)] [(6, 1), (18, 1)] (by simp [thSlpFacts]) (by decide)
      (by decide)
  have h8 : regUnit (spec2 248) hC 8 = regUnit (spec2 248) hC 7 ^ 2 := by
    simpa [wordUnit] using key [(8, 1)] [(7, 2)] (by simp [thSlpFacts]) (by decide) (by decide)
  have h15 : regUnit (spec2 248) hC 15 = regUnit (spec2 248) hC 14 ^ 18 := by
    simpa [wordUnit] using key [(15, 1)] [(14, 18)] (by simp [thSlpFacts]) (by decide) (by decide)
  have h17 : regUnit (spec2 248) hC 17 = regUnit (spec2 248) hC 16 ^ 14 := by
    simpa [wordUnit] using key [(17, 1)] [(16, 14)] (by simp [thSlpFacts]) (by decide) (by decide)
  have h18 : regUnit (spec2 248) hC 18 = regUnit (spec2 248) hC 9 ^ 9 := by
    simpa [wordUnit] using key [(18, 1)] [(9, 9)] (by simp [thSlpFacts]) (by decide) (by decide)
  have e2 : thEquivJ (regUnit (spec2 248) hC 2) = Max3.Slp.t3 := by rw [h2, map_mul, e0, e1]; rfl
  have e3 : thEquivJ (regUnit (spec2 248) hC 3) = Max3.Slp.t4 := by rw [h3, map_mul, e2, e1]; rfl
  have e4 : thEquivJ (regUnit (spec2 248) hC 4) = Max3.Slp.t5 := by rw [h4, map_mul, e2, e3]; rfl
  have e5 : thEquivJ (regUnit (spec2 248) hC 5) = Max3.Slp.t6 := by rw [h5, map_mul, e2, e4]; rfl
  have e6 : thEquivJ (regUnit (spec2 248) hC 6) = Max3.Slp.t7 := by rw [h6, map_mul, e0, e5]; rfl
  have e7 : thEquivJ (regUnit (spec2 248) hC 7) = Max3.Slp.t8 := by rw [h7, map_mul, e5, e0]; rfl
  have e8 : thEquivJ (regUnit (spec2 248) hC 8) = Max3.Slp.t8⁻¹ := by
    rw [h8, map_pow, e7, Max3.t8_inv]
  have e9 : thEquivJ (regUnit (spec2 248) hC 9) = Max3.Slp.u := by rw [h9, map_mul, e8, e6]; rfl
  have e10 : thEquivJ (regUnit (spec2 248) hC 10) = Max3.Slp.s8 := by
    rw [h10, map_mul, e5, e4]; rfl
  have e11 : thEquivJ (regUnit (spec2 248) hC 11) = Max3.Slp.s9 := by
    rw [h11, map_mul, e2, e10]; rfl
  have e12 : thEquivJ (regUnit (spec2 248) hC 12) = Max3.Slp.s10 := by
    rw [h12, map_mul, e11, e3]; rfl
  have e13 : thEquivJ (regUnit (spec2 248) hC 13) = Max3.Slp.s7 := by
    rw [h13, map_mul, e0, e12]; rfl
  have e14 : thEquivJ (regUnit (spec2 248) hC 14) = Max3.Slp.s8' := by
    rw [h14, map_mul, e12, e0]; rfl
  have e15 : thEquivJ (regUnit (spec2 248) hC 15) = Max3.Slp.s8'⁻¹ := by
    rw [h15, map_pow, e14, Max3.s8'_inv]
  have e16 : thEquivJ (regUnit (spec2 248) hC 16) = Max3.Slp.v := by
    rw [h16, map_mul, e15, e13]; rfl
  have e17 : thEquivJ (regUnit (spec2 248) hC 17) = Max3.x := by
    rw [h17, map_pow, e16]; rfl
  have e18 : thEquivJ (regUnit (spec2 248) hC 18) = Max3.Slp.u ^ 9 := by
    rw [h18, map_pow, e9]
  have e19 : thEquivJ (regUnit (spec2 248) hC 19) = Max3.y := by
    rw [h19, map_mul, e6, e18]; rfl
  exact ⟨e0, e1, e17, e19⟩

end

end CFSG.AGLEmbedding.R3
