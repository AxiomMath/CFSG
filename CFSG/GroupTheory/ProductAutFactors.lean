module

public import CFSG.LocalAnalysis.EvenSporadicStandard.M24Std.ProdAut
public import CFSG.RankThree.PartOne.KS.Basic

public section

namespace CFSG.GroupTheory

open Subgroup CFSG.EvenSporadicStandard.M24Std
open CFSG.ComponentClassification.OuterAutomorphisms (Outer)

variable {A B : Type*}

@[expose] noncomputable def mulAutProdHom (A B : Type*) [Group A] [Group B] :
    MulAut A × MulAut B →* MulAut (A × B) where
  toFun fg := MulEquiv.prodCongr fg.1 fg.2
  map_one' := by ext <;> rfl
  map_mul' _ _ := by ext <;> rfl

theorem mulAutProdHom_apply [Group A] [Group B] (f : MulAut A) (g : MulAut B) (a : A) (b : B) :
    mulAutProdHom A B (f, g) (a, b) = (f a, g b) := rfl

theorem mulAutProdHom_injective (A B : Type*) [Group A] [Group B] :
    Function.Injective (mulAutProdHom A B) := by
  rintro ⟨f₁, g₁⟩ ⟨f₂, g₂⟩ h
  have h1 : f₁ = f₂ := by
    ext a
    have := congrArg (fun e : MulAut (A × B) => (e (a, 1)).1) h
    simpa [mulAutProdHom_apply] using this
  have h2 : g₁ = g₂ := by
    ext b
    have := congrArg (fun e : MulAut (A × B) => (e (1, b)).2) h
    simpa [mulAutProdHom_apply] using this
  exact Prod.ext h1 h2

theorem exists_mulAut_prod_eq [Group A] [Group B] [Finite A] [Finite B] (α : MulAut (A × B))
    (h1 : ∀ a : A, (α (a, 1)).2 = 1) (h2 : ∀ b : B, (α (1, b)).1 = 1) :
    ∃ f : MulAut A, ∃ g : MulAut B, α = mulAutProdHom A B (f, g) := by
  let f : A →* A := (MonoidHom.fst A B).comp (α.toMonoidHom.comp (MonoidHom.inl A B))
  let g : B →* B := (MonoidHom.snd A B).comp (α.toMonoidHom.comp (MonoidHom.inr A B))
  have hf_apply : ∀ a : A, f a = (α (a, 1)).1 := fun _ => rfl
  have hg_apply : ∀ b : B, g b = (α (1, b)).2 := fun _ => rfl
  have hf_inj : Function.Injective f := by
    intro a a' h
    have hα : α (a, 1) = α (a', 1) :=
      Prod.ext h (by rw [h1 a, h1 a'])
    exact (Prod.ext_iff.mp (α.injective hα)).1
  have hg_inj : Function.Injective g := by
    intro b b' h
    have hα : α (1, b) = α (1, b') :=
      Prod.ext (by rw [h2 b, h2 b']) h
    exact (Prod.ext_iff.mp (α.injective hα)).2
  let f' : MulAut A := MulEquiv.ofBijective f ⟨hf_inj, Finite.surjective_of_injective hf_inj⟩
  let g' : MulAut B := MulEquiv.ofBijective g ⟨hg_inj, Finite.surjective_of_injective hg_inj⟩
  refine ⟨f', g', ?_⟩
  refine MulEquiv.ext (fun x => ?_)
  obtain ⟨a, b⟩ := x
  have hx : α (a, 1) = (f' a, 1) := Prod.ext (hf_apply a).symm (h1 a)
  have hy : α (1, b) = (1, g' b) := Prod.ext (h2 b) (hg_apply b).symm
  calc α (a, b) = α ((a, 1) * (1, b)) := by rw [Prod.mk_mul_mk, mul_one, one_mul]
    _ = α (a, 1) * α (1, b) := map_mul α (a, 1) (1, b)
    _ = (f' a, 1) * (1, g' b) := by rw [hx, hy]
    _ = (f' a, g' b) := by simp
    _ = mulAutProdHom A B (f', g') (a, b) := (mulAutProdHom_apply f' g' a b).symm

theorem le_fst_of_normal_of_card_eq [Group A] [Group B] [Finite A] [Finite B]
    [IsSimpleGroup B]
    (hcard : Nat.card A ≠ Nat.card B) {M : Subgroup (A × B)}
    (hMnormal : M.Normal) (hMsimple : IsSimpleGroup M)
    (hMcard : Nat.card M = Nat.card A) :
    M ≤ (⊤ : Subgroup A).prod (⊥ : Subgroup B) := by
  letI : M.Normal := hMnormal
  letI : IsSimpleGroup M := hMsimple
  let q : M →* B := (MonoidHom.snd A B).comp M.subtype
  have hq : q = 1 := by
    rcases (MonoidHom.normal_ker q).eq_bot_or_eq_top with hker | hker
    · have hqinj : Function.Injective q := (MonoidHom.ker_eq_bot_iff q).mp hker
      have hqrange_normal : q.range.Normal := by
        refine ⟨fun b hb g => ?_⟩
        obtain ⟨m, rfl⟩ := hb
        refine ⟨⟨(1, g) * (m : A × B) * (1, g)⁻¹,
          hMnormal.conj_mem (m : A × B) m.2 (1, g)⟩, ?_⟩
        simp [q]
      rcases hqrange_normal.eq_bot_or_eq_top with hbot | htop
      · exact MonoidHom.range_eq_bot_iff.mp hbot
      · exfalso
        have hqsurj : Function.Surjective q := MonoidHom.range_eq_top.mp htop
        have hcardMB : Nat.card M = Nat.card B :=
          Nat.card_congr (Equiv.ofBijective q ⟨hqinj, hqsurj⟩)
        exact hcard (hMcard.symm.trans hcardMB)
    · exact MonoidHom.ker_eq_top_iff.mp hker
  intro m hm
  have h2 : (m : A × B).2 = 1 := by
    have := congrArg (fun f : M →* B => f ⟨m, hm⟩) hq
    simpa [q] using this
  exact Subgroup.mem_prod.mpr ⟨Subgroup.mem_top _, by simpa using h2⟩

theorem le_snd_of_normal_of_card_eq [Group A] [Group B] [Finite A] [Finite B]
    [IsSimpleGroup A]
    (hcard : Nat.card A ≠ Nat.card B) {M : Subgroup (A × B)}
    (hMnormal : M.Normal) (hMsimple : IsSimpleGroup M)
    (hMcard : Nat.card M = Nat.card B) :
    M ≤ (⊥ : Subgroup A).prod (⊤ : Subgroup B) := by
  letI : M.Normal := hMnormal
  letI : IsSimpleGroup M := hMsimple
  let p : M →* A := (MonoidHom.fst A B).comp M.subtype
  have hp : p = 1 := by
    rcases (MonoidHom.normal_ker p).eq_bot_or_eq_top with hker | hker
    · have hpinj : Function.Injective p := (MonoidHom.ker_eq_bot_iff p).mp hker
      have hprange_normal : p.range.Normal := by
        refine ⟨fun a ha g => ?_⟩
        obtain ⟨m, rfl⟩ := ha
        refine ⟨⟨(g, 1) * (m : A × B) * (g, 1)⁻¹,
          hMnormal.conj_mem (m : A × B) m.2 (g, 1)⟩, ?_⟩
        simp [p]
      rcases hprange_normal.eq_bot_or_eq_top with hbot | htop
      · exact MonoidHom.range_eq_bot_iff.mp hbot
      · exfalso
        have hpsurj : Function.Surjective p := MonoidHom.range_eq_top.mp htop
        have hcardMA : Nat.card M = Nat.card A :=
          Nat.card_congr (Equiv.ofBijective p ⟨hpinj, hpsurj⟩)
        exact hcard (hcardMA.symm.trans hMcard)
    · exact MonoidHom.ker_eq_top_iff.mp hker
  intro m hm
  have h1 : (m : A × B).1 = 1 := by
    have := congrArg (fun f : M →* A => f ⟨m, hm⟩) hp
    simpa [p] using this
  exact Subgroup.mem_prod.mpr ⟨by simpa using h1, Subgroup.mem_top _⟩

theorem mulAut_prod_factors_of_card_ne [Group A] [Group B] [Finite A] [Finite B]
    [IsSimpleGroup A] [IsSimpleGroup B] (hcard : Nat.card A ≠ Nat.card B) (α : MulAut (A × B)) :
    (∀ a : A, (α (a, 1)).2 = 1) ∧ (∀ b : B, (α (1, b)).1 = 1) := by
  let F : Subgroup (A × B) := (⊤ : Subgroup A).prod (⊥ : Subgroup B)
  let G : Subgroup (A × B) := (⊥ : Subgroup A).prod (⊤ : Subgroup B)
  have hFnormal : F.Normal := Subgroup.prod_normal ⊤ ⊥
  have hGnormal : G.Normal := Subgroup.prod_normal ⊥ ⊤
  have hFmap_normal : (F.map α.toMonoidHom).Normal := hFnormal.map α.toMonoidHom α.surjective
  have hGmap_normal : (G.map α.toMonoidHom).Normal := hGnormal.map α.toMonoidHom α.surjective
  have hFmap_simple : IsSimpleGroup (F.map α.toMonoidHom) := by
    let e : (F.map α.toMonoidHom) ≃* A :=
      ((Subgroup.equivMapOfInjective F α.toMonoidHom α.injective).symm.trans
        ((Subgroup.prodEquiv (⊤ : Subgroup A) (⊥ : Subgroup B)).trans
          MulEquiv.prodUnique)).trans Subgroup.topEquiv
    exact e.isSimpleGroup
  have hGmap_simple : IsSimpleGroup (G.map α.toMonoidHom) := by
    let e : (G.map α.toMonoidHom) ≃* B :=
      ((Subgroup.equivMapOfInjective G α.toMonoidHom α.injective).symm.trans
        ((Subgroup.prodEquiv (⊥ : Subgroup A) (⊤ : Subgroup B)).trans
          MulEquiv.uniqueProd)).trans Subgroup.topEquiv
    exact e.isSimpleGroup
  have hFmap_card : Nat.card (F.map α.toMonoidHom) = Nat.card A := by
    rw [Subgroup.card_map_of_injective α.injective]
    exact Nat.card_congr (((Subgroup.prodEquiv (⊤ : Subgroup A) (⊥ : Subgroup B)).trans
      MulEquiv.prodUnique).trans Subgroup.topEquiv).toEquiv
  have hGmap_card : Nat.card (G.map α.toMonoidHom) = Nat.card B := by
    rw [Subgroup.card_map_of_injective α.injective]
    exact Nat.card_congr (((Subgroup.prodEquiv (⊥ : Subgroup A) (⊤ : Subgroup B)).trans
      MulEquiv.uniqueProd).trans Subgroup.topEquiv).toEquiv
  have hFmap_le : F.map α.toMonoidHom ≤ F :=
    le_fst_of_normal_of_card_eq (A := A) (B := B) hcard hFmap_normal hFmap_simple hFmap_card
  have hGmap_le : G.map α.toMonoidHom ≤ G :=
    le_snd_of_normal_of_card_eq (A := A) (B := B) hcard hGmap_normal hGmap_simple hGmap_card
  have hFmap_eq : F.map α.toMonoidHom = F := by
    refine Subgroup.eq_of_le_of_card_ge hFmap_le ?_
    rw [hFmap_card]
    exact le_of_eq (Nat.card_congr (((Subgroup.prodEquiv (⊤ : Subgroup A)
      (⊥ : Subgroup B)).trans MulEquiv.prodUnique).trans Subgroup.topEquiv).toEquiv)
  have hGmap_eq : G.map α.toMonoidHom = G := by
    refine Subgroup.eq_of_le_of_card_ge hGmap_le ?_
    rw [hGmap_card]
    exact le_of_eq (Nat.card_congr (((Subgroup.prodEquiv (⊥ : Subgroup A)
      (⊤ : Subgroup B)).trans MulEquiv.uniqueProd).trans Subgroup.topEquiv).toEquiv)
  constructor
  · intro a
    have hmem : α (a, 1) ∈ F.map α.toMonoidHom :=
      Subgroup.mem_map.mpr ⟨(a, 1), Subgroup.mem_prod.mpr ⟨Subgroup.mem_top _, by simp⟩, rfl⟩
    rw [hFmap_eq] at hmem
    exact Subgroup.mem_bot.mp (Subgroup.mem_prod.mp hmem).2
  · intro b
    have hmem : α (1, b) ∈ G.map α.toMonoidHom :=
      Subgroup.mem_map.mpr ⟨(1, b), Subgroup.mem_prod.mpr ⟨by simp, Subgroup.mem_top _⟩, rfl⟩
    rw [hGmap_eq] at hmem
    exact Subgroup.mem_bot.mp (Subgroup.mem_prod.mp hmem).1

theorem card_mulAut_prod_of_card_ne [Group A] [Group B] [Finite A] [Finite B]
    [IsSimpleGroup A] [IsSimpleGroup B]
    (hcard : Nat.card A ≠ Nat.card B) :
    Nat.card (MulAut (A × B)) = Nat.card (MulAut A) * Nat.card (MulAut B) := by
  have hsurj : Function.Surjective (mulAutProdHom A B) := by
    intro α
    obtain ⟨h1, h2⟩ := mulAut_prod_factors_of_card_ne hcard α
    obtain ⟨f, g, hfg⟩ := exists_mulAut_prod_eq α h1 h2
    exact ⟨(f, g), hfg.symm⟩
  have hbij : Function.Bijective (mulAutProdHom A B) :=
    ⟨mulAutProdHom_injective A B, hsurj⟩
  calc Nat.card (MulAut (A × B)) = Nat.card (MulAut A × MulAut B) :=
        (Nat.card_congr (Equiv.ofBijective (mulAutProdHom A B) hbij)).symm
    _ = Nat.card (MulAut A) * Nat.card (MulAut B) := Nat.card_prod _ _

theorem card_mulAut_square_dvd [Group A] [Finite A] [IsSimpleGroup A]
    (hsimple : ∀ N : Subgroup A, N.Normal → N = ⊥ ∨ N = ⊤)
    (hcentral : ∀ a : A, (∀ c : A, a * c = c * a) → a = 1)
    (hnt : ∃ s : A, s ≠ 1) :
    Nat.card (MulAut (A × A)) ∣ 2 * Nat.card (MulAut A) ^ 2 := by
  let P : Subgroup (MulAut (A × A)) := (mulAutProdHom A A).range
  let swap : MulAut (A × A) := MulEquiv.prodComm
  have hPcard : Nat.card P = Nat.card (MulAut A) ^ 2 := by
    dsimp [P]
    rw [(Nat.card_congr (MonoidHom.ofInjective
      (mulAutProdHom_injective A A)).toEquiv).symm, Nat.card_prod, pow_two]
  have hPindex : P.index ∣ 2 := by
    refine Subgroup.index_dvd_two_iff.mpr ⟨swap, fun α => ?_⟩
    rcases ProdAut.mulAut_prod_cases hsimple hcentral hnt α with
      ⟨hα1, hα2⟩ | ⟨hα1, hα2⟩
    · right
      obtain ⟨f, g, hfg⟩ := ProdAut.exists_prod_preserve α hα1 hα2
      refine ⟨(f, g), ?_⟩
      refine MulEquiv.ext (fun x => ?_)
      obtain ⟨a, b⟩ := x
      exact (hfg a b).symm
    · left
      have hβ1 : ∀ a : A, ((α * swap) (a, 1)).2 = 1 := by
        intro a
        change (α (swap (a, 1))).2 = 1
        rw [show swap (a, 1) = (1, a) from rfl]
        exact hα2 a
      have hβ2 : ∀ a : A, ((α * swap) (1, a)).1 = 1 := by
        intro a
        change (α (swap (1, a))).1 = 1
        rw [show swap (1, a) = (a, 1) from rfl]
        exact hα1 a
      obtain ⟨f, g, hfg⟩ := ProdAut.exists_prod_preserve (α * swap) hβ1 hβ2
      refine ⟨(f, g), ?_⟩
      refine MulEquiv.ext (fun x => ?_)
      obtain ⟨a, b⟩ := x
      exact (hfg a b).symm
  have hcard : Nat.card (MulAut (A × A)) = Nat.card P * P.index :=
    (Subgroup.card_mul_index P).symm
  rw [hcard, hPcard]
  have hdvd := Nat.mul_dvd_mul_left (Nat.card (MulAut A) ^ 2) hPindex
  rwa [mul_comm (Nat.card (MulAut A) ^ 2) 2] at hdvd

theorem isPGroup_outer_prod_of_card_ne [Group A] [Group B] [Finite A] [Finite B]
    [IsSimpleGroup A] [IsSimpleGroup B] (hcard : Nat.card A ≠ Nat.card B)
    (hZA : Subgroup.center A = ⊥) (hZB : Subgroup.center B = ⊥)
    (hA : IsPGroup 2 (Outer A)) (hB : IsPGroup 2 (Outer B)) :
    IsPGroup 2 (Outer (A × B)) := by
  have hZ : Subgroup.center (A × B) = ⊥ := by
    rw [Subgroup.center_prod, hZA, hZB, Subgroup.bot_prod_bot]
  have hAutAB := card_mulAut_prod_of_card_ne (A := A) (B := B) hcard
  have hAutA : Nat.card (MulAut A) = Nat.card (Outer A) * Nat.card A :=
    (CFSG.RankThree.PartOne.card_mulAut_eq_mul_card_outer hZA).trans (mul_comm _ _)
  have hAutB : Nat.card (MulAut B) = Nat.card (Outer B) * Nat.card B :=
    (CFSG.RankThree.PartOne.card_mulAut_eq_mul_card_outer hZB).trans (mul_comm _ _)
  have hAutZ : Nat.card (MulAut (A × B)) = Nat.card (Outer (A × B)) * Nat.card (A × B) :=
    (CFSG.RankThree.PartOne.card_mulAut_eq_mul_card_outer hZ).trans (mul_comm _ _)
  have hOutAB : Nat.card (Outer (A × B)) = Nat.card (Outer A) * Nat.card (Outer B) := by
    have hmain : Nat.card (Outer (A × B)) * (Nat.card A * Nat.card B) =
        (Nat.card (Outer A) * Nat.card A) * (Nat.card (Outer B) * Nat.card B) := by
      rw [← Nat.card_prod, ← hAutZ, hAutAB, hAutA, hAutB]
    have hpos : 0 < Nat.card A * Nat.card B := Nat.mul_pos Nat.card_pos Nat.card_pos
    have h' : Nat.card (Outer (A × B)) * (Nat.card A * Nat.card B) =
        (Nat.card (Outer A) * Nat.card (Outer B)) * (Nat.card A * Nat.card B) := by
      rw [hmain]
      ring
    exact Nat.eq_of_mul_eq_mul_right hpos h'
  obtain ⟨i, hi⟩ := hA.exists_card_eq
  obtain ⟨j, hj⟩ := hB.exists_card_eq
  have hcard : Nat.card (Outer (A × B)) = 2 ^ (i + j) := by
    rw [hOutAB, hi, hj, ← pow_add]
  exact IsPGroup.of_card hcard

theorem isPGroup_outer_square [Group A] [Finite A] [IsSimpleGroup A]
    (hsimple : ∀ N : Subgroup A, N.Normal → N = ⊥ ∨ N = ⊤)
    (hcentral : ∀ a : A, (∀ c : A, a * c = c * a) → a = 1)
    (hnt : ∃ s : A, s ≠ 1)
    (hZA : Subgroup.center A = ⊥)
    (hOutA : IsPGroup 2 (Outer A)) :
    IsPGroup 2 (Outer (A × A)) := by
  have hZ : Subgroup.center (A × A) = ⊥ := by
    rw [Subgroup.center_prod, hZA, Subgroup.bot_prod_bot]
  have hdvdAut : Nat.card (MulAut (A × A)) ∣ 2 * Nat.card (MulAut A) ^ 2 :=
    card_mulAut_square_dvd hsimple hcentral hnt
  have hAutA : Nat.card (MulAut A) = Nat.card (Outer A) * Nat.card A :=
    (CFSG.RankThree.PartOne.card_mulAut_eq_mul_card_outer hZA).trans (mul_comm _ _)
  have hAutZ : Nat.card (MulAut (A × A)) = Nat.card (Outer (A × A)) * Nat.card (A × A) :=
    (CFSG.RankThree.PartOne.card_mulAut_eq_mul_card_outer hZ).trans (mul_comm _ _)
  have hAutAA : Nat.card (MulAut (A × A)) =
      Nat.card (Outer (A × A)) * (Nat.card A) ^ 2 := by
    rw [hAutZ, Nat.card_prod, pow_two]
  have hdvd : Nat.card (Outer (A × A)) * (Nat.card A) ^ 2 ∣
      2 * (Nat.card (Outer A) * Nat.card A) ^ 2 := by
    rw [← hAutAA]
    rwa [hAutA] at hdvdAut
  have hdvd' : Nat.card (Outer (A × A)) * (Nat.card A) ^ 2 ∣
      (2 * Nat.card (Outer A) ^ 2) * (Nat.card A) ^ 2 := by
    convert hdvd using 1
    ring
  have hdvdOut : Nat.card (Outer (A × A)) ∣ 2 * Nat.card (Outer A) ^ 2 :=
    Nat.dvd_of_mul_dvd_mul_right (pow_pos Nat.card_pos 2) hdvd'
  obtain ⟨i, hi⟩ := hOutA.exists_card_eq
  have hpow : 2 * Nat.card (Outer A) ^ 2 = 2 ^ (2 * i + 1) := by
    rw [hi, ← pow_mul, mul_comm 2 (2 ^ (i * 2)), ← pow_succ]
    congr 1
    ring
  exact IsPGroup.of_card_dvd_pow (n := 2 * i + 1) (by rwa [hpow] at hdvdOut)

end CFSG.GroupTheory
