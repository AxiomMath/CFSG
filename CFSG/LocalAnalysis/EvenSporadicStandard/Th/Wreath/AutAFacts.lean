module

public import CFSG.LocalAnalysis.EvenSporadicStandard.Th.Wreath.NormalizerDAction
public import CFSG.LocalAnalysis.EvenSporadicStandard.Th.SingerCoord
public import CFSG.LocalAnalysis.EvenSporadicStandard.Th.GL4Rep

public section

namespace CFSG.EvenSporadicStandard.ThStd

open Subgroup Matrix LinearMap

variable {G : Type} [Group G] [Finite G] {L R : Subgroup G} {t : G} {S A B Aa D : Subgroup G}
  {z b : G}

private abbrev HnSub (L A : Subgroup G) : Subgroup G := L ⊓ normalizer (A : Set G)

private abbrev V4 : Type := Fin 4 → ZMod 2

private instance : AddCommGroup V4 := inferInstanceAs (AddCommGroup (Fin 4 → ZMod 2))
private instance : Module (ZMod 2) V4 := inferInstanceAs (Module (ZMod 2) (Fin 4 → ZMod 2))

private noncomputable def normHom (L A : Subgroup G) : ↥(HnSub L A) →* MulAut ↥A :=
  (Subgroup.normalizerMonoidHom (H := A)).comp
    (Subgroup.inclusion fun _ hx => hx.2)

private theorem normHom_apply (n : ↥(HnSub L A)) (a : ↥A) :
    ((normHom L A n a : ↥A) : G) = (n : G) * (a : G) * (n : G)⁻¹ := by
  rw [normHom, MonoidHom.comp_apply, Subgroup.normalizerMonoidHom_apply_apply_coe]
  rfl

private theorem normHom_surjective (W : ThLocalIn L S A B z) :
    Function.Surjective (normHom L A) := by
  intro φ
  classical
  let f : G → G := fun a => if ha : a ∈ A then ((φ ⟨a, ha⟩ : ↥A) : G) else 1
  have hfA : ∀ a ∈ A, f a ∈ A := by
    intro a ha
    dsimp [f]
    rw [dif_pos ha]
    exact (φ ⟨a, ha⟩).2
  have hfmul : ∀ a ∈ A, ∀ b ∈ A, f (a * b) = f a * f b := by
    intro a ha b hb
    dsimp [f]
    rw [dif_pos (A.mul_mem ha hb), dif_pos ha, dif_pos hb]
    exact congrArg (fun x : ↥A => (x : G)) (φ.map_mul ⟨a, ha⟩ ⟨b, hb⟩)
  have hfinj : ∀ a ∈ A, ∀ b ∈ A, f a = f b → a = b := by
    intro a ha b hb hab
    dsimp [f] at hab
    rw [dif_pos ha, dif_pos hb] at hab
    exact congrArg (fun x : ↥A => (x : G)) (φ.injective (Subtype.ext hab))
  obtain ⟨n, hnL, hn⟩ := W.surj f hfA hfmul hfinj
  have hnA : ∀ a ∈ A, n * a * n⁻¹ ∈ A := fun a ha => by
    rw [hn a ha]
    exact hfA a ha
  have hmaple : A.map (MulAut.conj n).toMonoidHom ≤ A := by
    rintro _ ⟨a, ha, rfl⟩
    simpa [MulAut.conj_apply] using hnA a ha
  have hcardmap : Nat.card (A.map (MulAut.conj n).toMonoidHom) = Nat.card A :=
    Subgroup.card_map_of_injective (K := A) (f := (MulAut.conj n).toMonoidHom)
      (MulAut.conj n).injective
  have hmapeq : A.map (MulAut.conj n).toMonoidHom = A :=
    Subgroup.eq_of_le_of_card_ge hmaple (by rw [hcardmap])
  have hnN : n ∈ normalizer (A : Set G) :=
    Subgroup.mem_normalizer_iff_map_conj_eq.2 hmapeq
  refine ⟨⟨n, hnL, hnN⟩, ?_⟩
  apply MulEquiv.ext
  intro a
  apply Subtype.ext
  rw [normHom_apply, hn (a : G) a.2]
  simp [f, a.2]

private theorem normHom_ker (W : ThLocalIn L S A B z) :
    (normHom L A).ker = B.subgroupOf (HnSub L A) := by
  ext x
  rw [MonoidHom.mem_ker, Subgroup.mem_subgroupOf]
  constructor
  · intro h
    refine (W.mem_B_iff (x : G) x.2.1).2 fun a ha => ?_
    have hconj := congrArg (fun ψ : MulAut ↥A => ((ψ ⟨a, ha⟩ : ↥A) : G)) h
    rw [normHom_apply] at hconj
    have hxa : (x : G) * a * (x : G)⁻¹ = a := by
      simpa [MulAut.one_apply] using hconj
    calc (x : G) * a = ((x : G) * a * (x : G)⁻¹) * (x : G) := by group
      _ = a * (x : G) := by rw [hxa]
  · intro hxB
    refine MulEquiv.ext fun a => Subtype.ext ?_
    have hc := (W.mem_B_iff (x : G) x.2.1).1 hxB a a.2
    rw [normHom_apply, MulAut.one_apply]
    calc (x : G) * (a : G) * (x : G)⁻¹ = ((a : G) * (x : G)) * (x : G)⁻¹ := by rw [hc]
      _ = (a : G) := by group

private noncomputable def quotientHomEquiv (W : ThLocalIn L S A B z) :
    (↥(HnSub L A) ⧸ (normHom L A).ker) ≃* MulAut ↥A :=
  QuotientGroup.quotientKerEquivOfSurjective (normHom L A) (normHom_surjective W)

private theorem isSimpleGroup_quotientHom (W : ThLocalIn L S A B z) :
    IsSimpleGroup (↥(HnSub L A) ⧸ (normHom L A).ker) := by
  haveI : IsSimpleGroup (MulAut ↥A) := ThLocalIn.isSimpleGroup_mulAut_A W
  exact MulEquiv.isSimpleGroup (quotientHomEquiv W)

private theorem card_quotientHom (W : ThLocalIn L S A B z) :
    Nat.card (↥(HnSub L A) ⧸ (normHom L A).ker) = 20160 := by
  rw [Nat.card_congr (quotientHomEquiv W).toEquiv, ThLocalIn.card_mulAut_A W]

theorem ThLocalIn.eq_of_forall_conj_eq (W : ThLocalIn L S A B z) {a a' v : G}
    (ha : a ∈ A) (ha' : a' ∈ A) (hv : v ∈ A)
    (hfix : ∀ n ∈ L ⊓ normalizer (A : Set G), n * a * n⁻¹ = a → n * a' * n⁻¹ = a' →
      n * v * n⁻¹ = v) :
    v = 1 ∨ v = a ∨ v = a' ∨ v = a * a' := by
  classical
  by_contra hcon
  obtain ⟨k, c, j, hkL, hkA, hkodd, hkfix, hj, hcmul, hcinj, hconto, hcrep⟩ :=
    exists_singer_coord W.A_comm W.A_sq W.A_card W.surj
  have hc1 : c 1 = 0 := by
    have h := hcmul 1 A.one_mem 1 A.one_mem
    rw [one_mul] at h
    have h2 : c 1 + 0 = c 1 + c 1 := by
      rw [add_zero]
      exact h
    exact (add_left_cancel h2).symm
  let p : Submodule (ZMod 2) V4 :=
    Submodule.span (ZMod 2) ({c a, c a'} : Set V4)
  have hmem_span : c v ∉ p := by
    intro hmem
    obtain ⟨x, y, hxy⟩ := Submodule.mem_span_pair.mp hmem
    have hx01 : x = 0 ∨ x = 1 :=
      (show ∀ t : ZMod 2, t = 0 ∨ t = 1 from by decide) x
    have hy01 : y = 0 ∨ y = 1 :=
      (show ∀ t : ZMod 2, t = 0 ∨ t = 1 from by decide) y
    rcases hx01 with rfl | rfl <;> rcases hy01 with rfl | rfl
    · simp only [zero_smul, zero_add] at hxy
      exact hcon (Or.inl (hcinj v hv 1 A.one_mem (by rw [hc1]; exact hxy.symm)))
    · simp only [zero_smul, one_smul, zero_add, add_zero] at hxy
      exact hcon (Or.inr (Or.inr (Or.inl (hcinj v hv a' ha' hxy.symm))))
    · simp only [zero_smul, one_smul, zero_add, add_zero] at hxy
      exact hcon (Or.inr (Or.inl (hcinj v hv a ha hxy.symm)))
    · simp only [one_smul, zero_smul, zero_add, add_zero] at hxy
      have hcaa : c (a * a') = c a + c a' := hcmul a ha a' ha'
      exact hcon (Or.inr (Or.inr (Or.inr
        (hcinj v hv (a * a') (A.mul_mem ha ha') (by rw [← hxy]; exact hcaa.symm)))))
  obtain ⟨φ, hφv, hpker⟩ := Submodule.exists_le_ker_of_notMem hmem_span
  have hφv1 : φ (c v) = 1 := by
    rcases (show ∀ t : ZMod 2, t = 0 ∨ t = 1 from by decide) (φ (c v)) with h | h
    · exact absurd h hφv
    · exact h
  have hvsum : c v = ∑ i, c v i • (Pi.single i (1 : ZMod 2) : V4) := by
    ext j
    rw [Finset.sum_apply]
    rw [Finset.sum_eq_single j]
    · simp
    · intro b _ hbj
      simp only [Pi.smul_apply, Pi.single_eq_of_ne (Ne.symm hbj), smul_eq_mul, mul_zero]
    · intro hj
      simp at hj
  have hbasis : ∃ i : Fin 4, φ (Pi.single i (1 : ZMod 2) : V4) = 1 := by
    by_contra h
    push Not at h
    have hzero : ∀ i, φ (Pi.single i (1 : ZMod 2) : V4) = 0 := by
      intro i
      rcases (show ∀ t : ZMod 2, t = 0 ∨ t = 1 from by decide)
        (φ (Pi.single i (1 : ZMod 2) : V4)) with h' | h'
      · exact h'
      · exact absurd h' (h i)
    have hmap : φ (c v) = 0 := by
      rw [hvsum]
      have hsum : ∀ (s : Finset (Fin 4)) (f : Fin 4 → V4),
          φ (∑ i ∈ s, f i) = ∑ i ∈ s, φ (f i) := by
        intro s
        induction s using Finset.induction_on with
        | empty => simp
        | insert a s ha ih =>
          intro f
          rw [Finset.sum_insert ha, Finset.sum_insert ha, φ.map_add, ih]
      rw [hsum]
      apply Finset.sum_eq_zero
      intro i _
      rw [φ.map_smul, hzero i, smul_zero]
    exact hφv hmap
  obtain ⟨i, hi⟩ := hbasis
  let e : Fin 4 → V4 := fun k => (Pi.single k (1 : ZMod 2) : V4)
  obtain ⟨u, hu_ne, hu_ker⟩ : ∃ u : V4, u ≠ 0 ∧ φ u = 0 := by
    by_cases hu : e i + c v = 0
    · let j : Fin 4 := if i = 0 then 1 else 0
      have hji : j ≠ i := by
        fin_cases i <;> simp [j]
      by_cases hj : φ (e j) = 0
      · refine ⟨e j, ?_, hj⟩
        intro h
        have := congrFun h j
        simp [e] at this
      · have hj1 : φ (e j) = 1 := by
          rcases (show ∀ t : ZMod 2, t = 0 ∨ t = 1 from by decide) (φ (e j)) with h | h
          · exact absurd h hj
          · exact h
        refine ⟨e i + e j, ?_, by rw [φ.map_add, hi, hj1]; decide⟩
        intro h
        have hval := congrFun h i
        simp [e, Pi.single_eq_of_ne (Ne.symm hji)] at hval
    · exact ⟨e i + c v, hu, by rw [φ.map_add, hi, hφv1]; decide⟩
  let g : V4 ≃ₗ[ZMod 2] V4 := LinearEquiv.transvection hu_ker
  have hg : ∀ x, g x = x + φ x • u := fun x => LinearEquiv.transvection.apply hu_ker x
  let M : Matrix (Fin 4) (Fin 4) (ZMod 2) :=
    LinearMap.toMatrix' (g : V4 →ₗ[ZMod 2] V4)
  have hMapply : ∀ x, M.mulVec x = g x := fun x => by
    rw [← Matrix.toLin'_apply, Matrix.toLin'_toMatrix']
    rfl
  have hM : Function.Injective M.mulVec := by
    intro x y hxy
    exact g.injective (by rw [← hMapply x, ← hMapply y]; exact hxy)
  obtain ⟨n, hnL, hnA, hnrep⟩ :=
    (show IsCoord A c from ⟨hcmul, hcinj, hconto⟩).exists_lift W.surj hM
  have hnN : n ∈ normalizer (A : Set G) :=
    Subgroup.mem_normalizer_iff_map_conj_eq.2 <|
      Subgroup.eq_of_le_of_card_ge
        (by
          rintro _ ⟨y, hy, rfl⟩
          simpa [MulAut.conj_apply] using hnA y hy)
        (by simpa using (Subgroup.card_map_of_injective (K := A)
              (f := (MulAut.conj n).toMonoidHom) (MulAut.conj n).injective).ge)
  have hφaa : φ (c a) = 0 := LinearMap.mem_ker.mp (hpker (Submodule.subset_span (by simp)))
  have hφaa' : φ (c a') = 0 := LinearMap.mem_ker.mp (hpker (Submodule.subset_span (by simp)))
  have hna : n * a * n⁻¹ = a := by
    have hca : c (n * a * n⁻¹) = c a := by
      rw [hnrep a ha, hMapply, hg, hφaa, zero_smul, add_zero]
    exact hcinj _ (hnA a ha) a ha hca
  have hna' : n * a' * n⁻¹ = a' := by
    have hca : c (n * a' * n⁻¹) = c a' := by
      rw [hnrep a' ha', hMapply, hg, hφaa', zero_smul, add_zero]
    exact hcinj _ (hnA a' ha') a' ha' hca
  have hnv : n * v * n⁻¹ ≠ v := by
    intro heq
    have hcv : c v + u = c v := by
      have h1 : c (n * v * n⁻¹) = c v + u := by
        rw [hnrep v hv, hMapply, hg, hφv1, one_smul]
      rw [← h1, heq]
    have hu0' : u = 0 := add_left_cancel (by rw [add_zero]; exact hcv)
    exact hu_ne hu0'
  exact hnv (hfix n ⟨hnL, hnN⟩ hna hna')

theorem ThLocalIn.eq_one_or_eq_self_of_conj (W : ThLocalIn L S A B z) (f : G → G)
    (hfA : ∀ a ∈ A, f a ∈ A)
    (hfmul : ∀ a ∈ A, ∀ a' ∈ A, f (a * a') = f a * f a')
    (hfH : ∀ n ∈ L ⊓ normalizer (A : Set G), ∀ a ∈ A, f (n * a * n⁻¹) = n * f a * n⁻¹) :
    (∀ a ∈ A, f a = 1) ∨ (∀ a ∈ A, f a = a) := by
  have hdich : ∀ y ∈ A, f y = 1 ∨ f y = y := by
    intro y hy
    have hfyA : f y ∈ A := hfA y hy
    have hfy : ∀ n ∈ L ⊓ normalizer (A : Set G), n * y * n⁻¹ = y → n * f y * n⁻¹ = f y := by
      intro n hn hny
      rw [← hfH n hn y hy, hny]
    rcases W.eq_of_forall_conj_eq hy hy hfyA (fun n hn hny _ => hfy n hn hny) with h | h | h | h
    · exact Or.inl h
    · exact Or.inr h
    · exact Or.inr h
    · left
      rw [h, ← sq, W.A_sq y hy]
  have hf1 : f 1 = 1 := by
    have h := hfmul 1 A.one_mem 1 A.one_mem
    rw [one_mul] at h
    have h2 : f 1 * 1 = f 1 * f 1 := by
      rw [mul_one]
      exact h
    exact (mul_left_cancel h2).symm
  by_cases hall : ∀ a ∈ A, f a = 1
  · exact Or.inl hall
  · right
    push Not at hall
    obtain ⟨a₀, ha₀, hfa₀ne⟩ := hall
    have hfa₀ : f a₀ = a₀ := (hdich a₀ ha₀).resolve_left hfa₀ne
    intro x hx
    by_cases hx1 : x = 1
    · subst hx1
      exact hf1
    · rcases hdich x hx with hfx | hfx
      · exfalso
        have hmem : a₀ * x ∈ A := A.mul_mem ha₀ hx
        have hfa : f (a₀ * x) = a₀ := by
          rw [hfmul a₀ ha₀ x hx, hfx, mul_one, hfa₀]
        rcases hdich (a₀ * x) hmem with h | h
        · rw [hfa] at h
          exact hfa₀ne (hfa₀.trans h)
        · rw [hfa] at h
          have hx1' : x = 1 := by
            have h2 : a₀ * 1 = a₀ * x := by
              rw [mul_one]
              exact h
            exact (mul_left_cancel h2).symm
          exact hx1 hx1'
      · exact hfx

theorem ThLocalIn.map_eq_one_of_card_lt (W : ThLocalIn L S A B z) {P : Type*} [Group P]
    [Finite P] (f : ↥(L ⊓ normalizer (A : Set G)) →* P) (hP : Nat.card P < 20160)
    (hB : ∀ x : ↥(L ⊓ normalizer (A : Set G)), (x : G) ∈ B → f x = 1) :
    ∀ x, f x = 1 := by
  classical
  let Hn := HnSub L A
  have hKle : B.subgroupOf Hn ≤ f.ker := by
    intro x hx
    rw [Subgroup.mem_subgroupOf] at hx
    rw [MonoidHom.mem_ker]
    exact hB x hx
  have hKnormal : (B.subgroupOf Hn).Normal := by
    rw [show B.subgroupOf Hn = (normHom L A).ker from (normHom_ker W).symm]
    infer_instance
  letI : (B.subgroupOf Hn).Normal := hKnormal
  let e : (Hn ⧸ B.subgroupOf Hn) ≃* (Hn ⧸ (normHom L A).ker) :=
    QuotientGroup.quotientMulEquivOfEq (normHom_ker W).symm
  haveI : IsSimpleGroup (Hn ⧸ (normHom L A).ker) := isSimpleGroup_quotientHom W
  haveI : IsSimpleGroup (Hn ⧸ B.subgroupOf Hn) := MulEquiv.isSimpleGroup e
  let g : Hn ⧸ B.subgroupOf Hn →* P := QuotientGroup.lift _ f hKle
  rcases Subgroup.Normal.eq_bot_or_eq_top g.ker with hbot | htop
  · have hinj : Function.Injective g := (MonoidHom.ker_eq_bot_iff g).mp hbot
    have hcard := Nat.card_le_card_of_injective g hinj
    have hQcard : Nat.card (Hn ⧸ B.subgroupOf Hn) = 20160 := by
      rw [Nat.card_congr e.toEquiv, card_quotientHom W]
    omega
  · intro x
    have hx : g (QuotientGroup.mk x) = 1 := by
      have hmem : QuotientGroup.mk x ∈ g.ker := by
        rw [htop]
        exact Subgroup.mem_top _
      exact MonoidHom.mem_ker.mp hmem
    rwa [QuotientGroup.lift_mk] at hx

theorem ThLocalIn.eq_B_or_eq_of_normal (W : ThLocalIn L S A B z) {N₀ : Subgroup G}
    (hN₀ : N₀ ≤ L ⊓ normalizer (A : Set G)) (hBN : B ≤ N₀)
    (hn : ∀ h ∈ L ⊓ normalizer (A : Set G), ∀ x ∈ N₀, h * x * h⁻¹ ∈ N₀) :
    N₀ = B ∨ N₀ = L ⊓ normalizer (A : Set G) := by
  classical
  let Hn := HnSub L A
  let K : Subgroup Hn := B.subgroupOf Hn
  have hKnormal : K.Normal := by
    rw [show K = (normHom L A).ker from (normHom_ker W).symm]
    infer_instance
  letI : K.Normal := hKnormal
  let π : Hn →* Hn ⧸ K := QuotientGroup.mk' K
  let N' : Subgroup Hn := N₀.subgroupOf Hn
  have hN'normal : N'.Normal := by
    refine ⟨fun x hx g => ?_⟩
    rw [Subgroup.mem_subgroupOf] at hx ⊢
    simpa using hn (g : G) g.2 (x : G) hx
  haveI : N'.Normal := hN'normal
  haveI : (N'.map π).Normal := hN'normal.map π (QuotientGroup.mk'_surjective K)
  let e : (Hn ⧸ K) ≃* (Hn ⧸ (normHom L A).ker) :=
    QuotientGroup.quotientMulEquivOfEq (normHom_ker W).symm
  haveI : IsSimpleGroup (Hn ⧸ (normHom L A).ker) := isSimpleGroup_quotientHom W
  haveI : IsSimpleGroup (Hn ⧸ K) := MulEquiv.isSimpleGroup e
  rcases Subgroup.Normal.eq_bot_or_eq_top (N'.map π) with hbot | htop
  · left
    refine le_antisymm ?_ hBN
    intro x hx
    have hxH : x ∈ Hn := hN₀ hx
    have hxmap : π ⟨x, hxH⟩ ∈ N'.map π :=
      Subgroup.mem_map.mpr ⟨⟨x, hxH⟩, by rw [Subgroup.mem_subgroupOf]; exact hx, rfl⟩
    rw [hbot] at hxmap
    have hx1 : π ⟨x, hxH⟩ = 1 := Subgroup.mem_bot.mp hxmap
    have hxK' : (⟨x, hxH⟩ : ↥Hn) ∈ (QuotientGroup.mk' K).ker :=
      MonoidHom.mem_ker.mpr hx1
    have hxK : (⟨x, hxH⟩ : ↥Hn) ∈ K := by
      rwa [QuotientGroup.ker_mk'] at hxK'
    exact Subgroup.mem_subgroupOf.mp hxK
  · right
    refine le_antisymm hN₀ ?_
    intro x hxH
    have hxmap : π ⟨x, hxH⟩ ∈ N'.map π := by
      rw [htop]
      exact Subgroup.mem_top _
    obtain ⟨y, hyN, hyq⟩ := Subgroup.mem_map.mp hxmap
    have hyN₀ : (y : G) ∈ N₀ := Subgroup.mem_subgroupOf.mp hyN
    have hq : π y = π ⟨x, hxH⟩ := hyq
    have hker' : (y⁻¹ * ⟨x, hxH⟩ : ↥Hn) ∈ (QuotientGroup.mk' K).ker := by
      rw [MonoidHom.mem_ker]
      rw [map_mul, map_inv, hq, inv_mul_cancel]
    have hker : (y⁻¹ * ⟨x, hxH⟩ : ↥Hn) ∈ K := by
      rwa [QuotientGroup.ker_mk'] at hker'
    have hB : ((y⁻¹ * ⟨x, hxH⟩ : ↥Hn) : G) ∈ B := Subgroup.mem_subgroupOf.mp hker
    have hmem : (y : G)⁻¹ * x ∈ N₀ := by
      exact hBN (by simpa using hB)
    have hxeq : x = (y : G) * ((y : G)⁻¹ * x) := by group
    rw [hxeq]
    exact N₀.mul_mem hyN₀ hmem

end CFSG.EvenSporadicStandard.ThStd
