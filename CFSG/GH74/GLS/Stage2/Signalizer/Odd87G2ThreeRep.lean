module

public import CFSG.GH74.GLS.Stage2.Signalizer.Odd87G2ThreeArr
public import CFSG.LieType.Chevalley.NativeHolds

public noncomputable section

namespace CFSG.GH74.GLS.Stage2.Signalizer.Odd87.G2ThreeCert

open CFSG.Blueprint.Chevalley CFSG.LieType.Ree CFSG.LieType.Chevalley Certificates.G2ThreeMax

theorem g2_root_inj {m m' : ℕ} (hm : m < g2Certificate.roots.length)
    (hm' : m' < g2Certificate.roots.length)
    (h : g2Certificate.root m = g2Certificate.root m') : m = m' := by
  have hn := Tag.rootCertificate_checkNodup Tag.G2
  simp only [RootCertificate.checkNodup, decide_eq_true_eq] at hn
  exact List.inj_on_of_nodup_map hn (List.mem_range.2 hm) (List.mem_range.2 hm')
    (congrArg List.ofFn h)

theorem toLabel_injective : Function.Injective (toLabel g2Certificate_check) := by
  rintro (j | m) (j' | m') h
  · simpa [toLabel] using h
  · simp [toLabel] at h
  · simp [toLabel] at h
  · simp only [toLabel, Sum.inr.injEq, Subtype.mk.injEq] at h
    exact congrArg Sum.inr (Fin.ext (g2_root_inj m.2 m'.2 h))

theorem idxOf_inj : ∀ a b : Fin 14, idxOf a.val = idxOf b.val → a = b := by decide

theorem idxOf_surj : ∀ x : Idx g2Certificate, ∃ n : Fin 14, idxOf n.val = x := by decide

@[expose] def labEquiv : Fin 14 ≃ Label Tag.G2 :=
  Equiv.ofBijective (fun n => toLabel g2Certificate_check (idxOf n.val))
    ⟨fun a b h => idxOf_inj a b (toLabel_injective h), fun l => by
      obtain ⟨x, rfl⟩ := surjective_toLabel g2Certificate_check l
      obtain ⟨n, hn⟩ := idxOf_surj x
      exact ⟨n, by simp [hn]⟩⟩

variable (F : Type) [Field F]

@[expose] def bas : Module.Basis (Fin 14) F (RootModule Tag.G2 F) :=
  Finsupp.basisSingleOne.reindex labEquiv.symm

@[expose] def θ : Module.End F (RootModule Tag.G2 F) ≃ₐ[F] Matrix (Fin 14) (Fin 14) F :=
  LinearMap.toMatrixAlgEquiv (bas F)

variable {F}

theorem θ_apply (f : Module.End F (RootModule Tag.G2 F)) (r b : Fin 14) :
    θ F f r b = f (Finsupp.single (labEquiv b) 1) (labEquiv r) := by
  simp [θ, bas, LinearMap.toMatrixAlgEquiv_apply]

theorem toVec_apply (u : Col g2Certificate) (r : Idx g2Certificate) :
    (toVec g2Certificate_check (ZMod 3) u) (toLabel g2Certificate_check r) =
      (coefZ u r : ZMod 3) := by
  rcases u with _ | ⟨a, n⟩
  · simp [coefZ]
  · simp only [toVec_some, coefZ, Finsupp.smul_apply, Finsupp.single_apply, smul_eq_mul]
    by_cases h : a = r
    · subst h; simp
    · have : toLabel g2Certificate_check a ≠ toLabel g2Certificate_check r :=
        fun e => h (toLabel_injective e)
      simp [h, this]

theorem cast_toNat_emod (x : ℤ) : (((x % 3).toNat : ℕ) : ZMod 3) = (x : ZMod 3) := by
  have h0 : 0 ≤ x % 3 := Int.emod_nonneg x (by norm_num)
  have h2 : (((x % 3).toNat : ℕ) : ℤ) = x % 3 := Int.toNat_of_nonneg h0
  have h3 : (((x % 3).toNat : ℕ) : ZMod 3) = ((((x % 3).toNat : ℕ) : ℤ) : ZMod 3) :=
    (Int.cast_natCast _).symm
  have h4 := ZMod.intCast_mod x 3
  rw [h3, h2]
  simpa using h4

theorem θ_xOp (i : Fin Tag.G2.rank) (c : ℤ) :
    θ (ZMod 3) (xOp Tag.G2 (ZMod 3) i (c : ZMod 3)) = M (xArr i c) := by
  ext r b
  rw [θ_apply]
  simp only [M, xArr, Matrix.of_apply]
  rw [ofFn_get _ (idx_lt r b)]
  have h1 : (14 * r.val + b.val) / 14 = r.val := by have := b.2; omega
  have h2 : (14 * r.val + b.val) % 14 = b.val := by have := b.2; omega
  simp only [h1, h2]
  rw [cast_toNat_emod]
  have hl : (labEquiv b) = toLabel g2Certificate_check (idxOf b.val) := rfl
  have hl' : (labEquiv r) = toLabel g2Certificate_check (idxOf r.val) := rfl
  rw [hl, hl', xOp_eq_sum_xCoeff]
  simp only [LinearMap.sum_apply, LinearMap.smul_apply, Finsupp.coe_finsetSum, Finset.sum_apply,
    Finsupp.smul_apply, smul_eq_mul]
  simp only [xCoeff_toLabel g2Certificate_check (ZMod 3) g2StringData_check, toVec_apply]
  simp only [xEntry, Int.cast_sum, Int.cast_mul, Int.cast_pow]

theorem θ_yOp (i : Fin Tag.G2.rank) (c : ℤ) :
    θ (ZMod 3) (yOp Tag.G2 (ZMod 3) i (c : ZMod 3)) = M (yArr i c) := by
  ext r b
  rw [θ_apply]
  simp only [M, yArr, Matrix.of_apply]
  rw [ofFn_get _ (idx_lt r b)]
  have h1 : (14 * r.val + b.val) / 14 = r.val := by have := b.2; omega
  have h2 : (14 * r.val + b.val) % 14 = b.val := by have := b.2; omega
  simp only [h1, h2]
  rw [cast_toNat_emod]
  have hl : (labEquiv b) = toLabel g2Certificate_check (idxOf b.val) := rfl
  have hl' : (labEquiv r) = toLabel g2Certificate_check (idxOf r.val) := rfl
  rw [hl, hl', yOp_eq_sum_yCoeff]
  simp only [LinearMap.sum_apply, LinearMap.smul_apply, Finsupp.coe_finsetSum, Finset.sum_apply,
    Finsupp.smul_apply, smul_eq_mul]
  simp only [yCoeff_toLabel g2Certificate_check (ZMod 3) g2StringData_check, toVec_apply]
  simp only [yEntry, Int.cast_sum, Int.cast_mul, Int.cast_pow]

@[expose] def ρ : ModGL Tag.G2 (ZMod 3) →* Matrix.GeneralLinearGroup (Fin 14) (ZMod 3) :=
  Units.map (θ (ZMod 3)).toRingEquiv.toRingHom.toMonoidHom

theorem ρ_injective :
    Function.Injective (ρ : ModGL Tag.G2 (ZMod 3) →* Matrix.GeneralLinearGroup (Fin 14) (ZMod 3)) := by
  intro g h hgh
  apply Units.ext
  apply (θ (ZMod 3)).injective
  exact congrArg Units.val hgh

abbrev G3 : Type := ↥(adjointGroup Tag.G2 (ZMod 3))

@[expose] def ρG : G3 →* Matrix.GeneralLinearGroup (Fin 14) (ZMod 3) :=
  ρ.comp (adjointGroup Tag.G2 (ZMod 3)).subtype

theorem ρG_injective : Function.Injective (ρG : G3 →* Matrix.GeneralLinearGroup (Fin 14) (ZMod 3)) := by
  intro g h hgh
  exact Subtype.ext (ρ_injective hgh)

@[expose] def i0 : Fin Tag.G2.rank := ⟨0, by decide⟩

@[expose] def i1 : Fin Tag.G2.rank := ⟨1, by decide⟩

@[expose] def gensG : ℕ → G3
  | 0 => xElement i0 ((1 : ℤ) : ZMod 3)
  | 1 => xElement i0 ((-1 : ℤ) : ZMod 3)
  | 2 => xElement i1 ((1 : ℤ) : ZMod 3)
  | 3 => xElement i1 ((-1 : ℤ) : ZMod 3)
  | 4 => yElement i0 ((1 : ℤ) : ZMod 3)
  | 5 => yElement i0 ((-1 : ℤ) : ZMod 3)
  | 6 => yElement i1 ((1 : ℤ) : ZMod 3)
  | 7 => yElement i1 ((-1 : ℤ) : ZMod 3)
  | _ => 1

theorem ρG_xElement (i : Fin Tag.G2.rank) (c : ℤ) :
    ((ρG (xElement i (c : ZMod 3)) : Matrix.GeneralLinearGroup (Fin 14) (ZMod 3)) : Mat3) =
      M (xArr i c) := θ_xOp i c

theorem ρG_yElement (i : Fin Tag.G2.rank) (c : ℤ) :
    ((ρG (yElement i (c : ZMod 3)) : Matrix.GeneralLinearGroup (Fin 14) (ZMod 3)) : Mat3) =
      M (yArr i c) := θ_yOp i c

theorem hρ_gens : ∀ k < 8,
    ((ρG (gensG k) : Matrix.GeneralLinearGroup (Fin 14) (ZMod 3)) : Mat3) = M (genArr k) := by
  intro k hk
  interval_cases k
  · exact ρG_xElement i0 1
  · exact ρG_xElement i0 (-1)
  · exact ρG_xElement i1 1
  · exact ρG_xElement i1 (-1)
  · exact ρG_yElement i0 1
  · exact ρG_yElement i0 (-1)
  · exact ρG_yElement i1 1
  · exact ρG_yElement i1 (-1)

theorem xElement_inv (i : Fin Tag.G2.rank) (c : ZMod 3) :
    (xElement i c)⁻¹ = xElement i (-c) := by
  apply Subtype.ext
  rw [Subgroup.coe_inv]
  apply Units.ext
  exact coe_xUnit_inv i c

theorem yElement_inv (i : Fin Tag.G2.rank) (c : ZMod 3) :
    (yElement i c)⁻¹ = yElement i (-c) := by
  apply Subtype.ext
  rw [Subgroup.coe_inv]
  apply Units.ext
  exact coe_yUnit_inv i c

theorem xElement_neg (i : Fin Tag.G2.rank) (c : ℤ) :
    xElement i ((-c : ℤ) : ZMod 3) = (xElement i (c : ZMod 3))⁻¹ := by
  rw [xElement_inv, Int.cast_neg]
  rfl

theorem yElement_neg (i : Fin Tag.G2.rank) (c : ℤ) :
    yElement i ((-c : ℤ) : ZMod 3) = (yElement i (c : ZMod 3))⁻¹ := by
  rw [yElement_inv, Int.cast_neg]
  rfl

theorem xElement_neg' (i : Fin Tag.G2.rank) (c : ℤ) :
    xElement i (c : ZMod 3) = (xElement i ((-c : ℤ) : ZMod 3))⁻¹ := by
  rw [xElement_neg, inv_inv]

theorem yElement_neg' (i : Fin Tag.G2.rank) (c : ℤ) :
    yElement i (c : ZMod 3) = (yElement i ((-c : ℤ) : ZMod 3))⁻¹ := by
  rw [yElement_neg, inv_inv]

theorem hinv_gens : ∀ k < 8, gensG (invK k) = (gensG k)⁻¹ := by
  intro k hk
  interval_cases k
  · exact xElement_neg i0 1
  · exact xElement_neg' i0 1
  · exact xElement_neg i1 1
  · exact xElement_neg' i1 1
  · exact yElement_neg i0 1
  · exact yElement_neg' i0 1
  · exact yElement_neg i1 1
  · exact yElement_neg' i1 1

theorem xElement_zero (i : Fin Tag.G2.rank) : xElement i (0 : ZMod 3) = 1 :=
  Subtype.ext (Units.ext (xOp_zero i))

theorem yElement_zero (i : Fin Tag.G2.rank) : yElement i (0 : ZMod 3) = 1 :=
  Subtype.ext (Units.ext (yOp_zero i))

theorem fin_rank_cases (i : Fin Tag.G2.rank) : i = i0 ∨ i = i1 := by
  obtain ⟨n, hn⟩ := i
  have : n < 2 := hn
  interval_cases n
  · exact Or.inl rfl
  · exact Or.inr rfl

theorem zmod3_cases :
    ∀ c : ZMod 3, c = 0 ∨ c = ((1 : ℤ) : ZMod 3) ∨ c = ((-1 : ℤ) : ZMod 3) := by
  decide

theorem xElement_mem (i : Fin Tag.G2.rank) (c : ZMod 3) :
    xElement i c ∈ Subgroup.closure (gensG '' {k | k < 8}) := by
  have h0 : gensG 0 ∈ Subgroup.closure (gensG '' {k | k < 8}) :=
    Subgroup.subset_closure ⟨0, by norm_num, rfl⟩
  have h1 : gensG 1 ∈ Subgroup.closure (gensG '' {k | k < 8}) :=
    Subgroup.subset_closure ⟨1, by norm_num, rfl⟩
  have h2 : gensG 2 ∈ Subgroup.closure (gensG '' {k | k < 8}) :=
    Subgroup.subset_closure ⟨2, by norm_num, rfl⟩
  have h3 : gensG 3 ∈ Subgroup.closure (gensG '' {k | k < 8}) :=
    Subgroup.subset_closure ⟨3, by norm_num, rfl⟩
  rcases fin_rank_cases i with rfl | rfl <;> rcases zmod3_cases c with rfl | rfl | rfl
  · rw [xElement_zero]; exact Subgroup.one_mem _
  · exact h0
  · exact h1
  · rw [xElement_zero]; exact Subgroup.one_mem _
  · exact h2
  · exact h3

theorem yElement_mem (i : Fin Tag.G2.rank) (c : ZMod 3) :
    yElement i c ∈ Subgroup.closure (gensG '' {k | k < 8}) := by
  have h4 : gensG 4 ∈ Subgroup.closure (gensG '' {k | k < 8}) :=
    Subgroup.subset_closure ⟨4, by norm_num, rfl⟩
  have h5 : gensG 5 ∈ Subgroup.closure (gensG '' {k | k < 8}) :=
    Subgroup.subset_closure ⟨5, by norm_num, rfl⟩
  have h6 : gensG 6 ∈ Subgroup.closure (gensG '' {k | k < 8}) :=
    Subgroup.subset_closure ⟨6, by norm_num, rfl⟩
  have h7 : gensG 7 ∈ Subgroup.closure (gensG '' {k | k < 8}) :=
    Subgroup.subset_closure ⟨7, by norm_num, rfl⟩
  rcases fin_rank_cases i with rfl | rfl <;> rcases zmod3_cases c with rfl | rfl | rfl
  · rw [yElement_zero]; exact Subgroup.one_mem _
  · exact h4
  · exact h5
  · rw [yElement_zero]; exact Subgroup.one_mem _
  · exact h6
  · exact h7

theorem closure_gensG : Subgroup.closure (gensG '' {k | k < 8}) = ⊤ := by
  rw [eq_top_iff]
  rintro ⟨g, hg⟩ -
  change g ∈ Subgroup.closure _ at hg
  induction hg using Subgroup.closure_induction with
  | mem x hx =>
    obtain ⟨i, c, hxc | hxc⟩ := hx
    · have : (⟨x, Subgroup.subset_closure ⟨i, c, Or.inl hxc⟩⟩ : G3) = xElement i c :=
        Subtype.ext (Units.ext hxc)
      rw [this]
      exact xElement_mem i c
    · have : (⟨x, Subgroup.subset_closure ⟨i, c, Or.inr hxc⟩⟩ : G3) = yElement i c :=
        Subtype.ext (Units.ext hxc)
      rw [this]
      exact yElement_mem i c
  | one => exact Subgroup.one_mem _
  | mul x y hx hy ihx ihy => exact Subgroup.mul_mem _ ihx ihy
  | inv x hx ih => exact Subgroup.inv_mem _ ih

end CFSG.GH74.GLS.Stage2.Signalizer.Odd87.G2ThreeCert
