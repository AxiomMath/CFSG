module

public import CFSG.GH74.GLS.IVK.Lifted.IIAutD
public import CFSG.Dihedral.Glauberman.DicksonMaxList
public import CFSG.LinearAlgebra.LinearGroups.TameProjectiveSubgroups
public import CFSG.Walter.Models

public section

namespace CFSG.GH74.GLS.IVK.Lifted

open Subgroup CFSG CFSG.GH74.GLS CFSG.GH74.GLS.Stage1.Thm2.Recip CFSG.Glauberman.Dickson
  CFSG.BenderSuzuki.MatrixGroups CFSG.GorensteinWalter CFSG.ABGLocalTools

theorem center_eq_one_of_simple_nonabelian {S : Type} [Group S] [IsSimpleGroup S]
    (hab : ∃ a b : S, a * b ≠ b * a) (s : S) (hs : s ∈ Subgroup.center S) : s = 1 := by
  rcases (inferInstance : (Subgroup.center S).Normal).eq_bot_or_eq_top with h | h
  · rw [h] at hs
    exact Subgroup.mem_bot.1 hs
  · exfalso
    obtain ⟨a, b, hne⟩ := hab
    apply hne
    have hb : b ∈ Subgroup.center S := by rw [h]; trivial
    exact Subgroup.mem_center_iff.1 hb a

theorem not_isSolvable_of_simple_nonabelian {S : Type} [Group S] [IsSimpleGroup S]
    (hab : ∃ a b : S, a * b ≠ b * a) : ¬ Group.IsSolvable S := by
  intro hsolv
  obtain ⟨a, b, hne⟩ := hab
  exact hne (IsSimpleGroup.comm_iff_isSolvable.2 hsolv a b)

theorem injective_of_surjective_simple {G S : Type} [Group G] [Group S] [IsSimpleGroup G]
    [Nontrivial S] (f : G →* S) (hf : Function.Surjective f) : Function.Injective f := by
  rw [← MonoidHom.ker_eq_bot_iff]
  rcases f.normal_ker.eq_bot_or_eq_top with h | h
  · exact h
  · exfalso
    obtain ⟨a, b, hab⟩ := exists_pair_ne S
    obtain ⟨x, rfl⟩ := hf a
    obtain ⟨y, rfl⟩ := hf b
    apply hab
    have hx : x ∈ f.ker := by rw [h]; trivial
    have hy : y ∈ f.ker := by rw [h]; trivial
    rw [MonoidHom.mem_ker.1 hx, MonoidHom.mem_ker.1 hy]

theorem prime_card_of_simple_abelian {G : Type} [Group G] [IsSimpleGroup G]
    (hab : ∀ a b : G, a * b = b * a) : (Nat.card G).Prime := by
  let _ : CommGroup G := { (inferInstance : Group G) with mul_comm := hab }
  exact IsSimpleGroup.prime_card

theorem isSolvable_of_card_two_three {G : Type} [Group G] [Finite G] {a b : ℕ}
    (h : Nat.card G = 2 ^ a * 3 ^ b) : Group.IsSolvable G := by
  have := Fintype.ofFinite G
  exact CFSG.Burnside.finite_group_isSolvable_of_card_eq_prime_pow_mul_prime_pow Nat.prime_two
    Nat.prime_three (by norm_num) (by rw [← Nat.card_eq_fintype_card, h])

theorem isSolvable_of_mulEquiv_lifted {X Y : Type} [Group X] [Group Y] (e : X ≃* Y)
    [Group.IsSolvable Y] : Group.IsSolvable X :=
  Group.isSolvable_of_isSolvable_injective (f := e.toMonoidHom) e.injective

theorem isSolvable_semidirectProduct {E C : Type} [Group E] [Group C] (φ : C →* MulAut E)
    [Group.IsSolvable E] [Group.IsSolvable C] : Group.IsSolvable (E ⋊[φ] C) :=
  Group.isSolvable_of_ker_le_range (SemidirectProduct.inl : E →* (E ⋊[φ] C))
    SemidirectProduct.rightHom (SemidirectProduct.range_inl_eq_ker_rightHom).ge

theorem not_nonabelian_of_map_eq_bot {R : Type} [Group R] (S : Type) [Group S] (R₀ : Subgroup R)
    (hidx : R₀.index = 2) (ρ' : R →* S) (hρ' : Function.Surjective ρ')
    (h0 : R₀.map ρ' = ⊥) (hab : ∃ a b : S, a * b ≠ b * a) : False := by
  have hle : R₀ ≤ ρ'.ker := fun x hx => by
    have : ρ' x ∈ R₀.map ρ' := ⟨x, hx, rfl⟩
    rw [h0, Subgroup.mem_bot] at this
    exact this
  have hdvd : (ρ'.ker).index ∣ 2 := by
    have := Subgroup.index_dvd_of_le hle
    rwa [hidx] at this
  have hcardS : Nat.card S = (ρ'.ker).index := by
    rw [Subgroup.index_ker, MonoidHom.range_eq_top.2 hρ', Subgroup.card_top]
  rw [← hcardS] at hdvd
  obtain ⟨a, b, hab'⟩ := hab
  rcases (Nat.dvd_prime Nat.prime_two).1 hdvd with h | h
  · have : Subsingleton S := (Nat.card_eq_one_iff_unique.1 h).1
    exact hab' (Subsingleton.elim _ _)
  · have hcyc : IsCyclic S := isCyclic_of_prime_card (p := 2) h
    exact hab' ((IsCyclic.isMulCommutative (α := S)).is_comm.comm a b)

theorem statedClassicalModel_psl_two_lifted {G : Type} [Group G] (p f : ℕ) [Fact p.Prime]
    (h4 : 4 ≤ p ^ f) (e : G ≃* Matrix.ProjectiveSpecialLinearGroup (Fin 2) (GaloisField p f)) :
    CFSG.Assembly.LowTwoRank.StatedClassicalModel G .PSL 2 p f := by
  obtain ⟨-, hc | ⟨hn, -⟩⟩ := CFSG.Walter.lieModel_psl_two_of_mulEquiv p f h4 e
  · exact hc
  · exact absurd hn (by decide)

theorem catalog_of_quotient_psl2 {p m : ℕ} [Fact p.Prime] (hp : Odd p) (hm : m ≠ 0) {S : Type}
    [Group S] [IsSimpleGroup S] (hab : ∃ a b : S, a * b ≠ b * a)
    (σ : PSL2MatrixGroup (GaloisField p m) →* S) (hσ : Function.Surjective σ) :
    CFSG.Blueprint.Catalog S := by
  have hcard : Nat.card (GaloisField p m) = p ^ m := GaloisField.card p m hm
  have hodd : Odd (p ^ m) := hp.pow
  have hp3 : 3 ≤ p := by
    obtain ⟨k, hk⟩ := hp
    have := (Fact.out : p.Prime).two_le
    omega
  have hpm : p ≤ p ^ m := Nat.le_self_pow hm p
  by_cases h3 : p ^ m = 3
  · exfalso
    apply not_isSolvable_of_simple_nonabelian hab
    have hc : Nat.card (Matrix.SpecialLinearGroup (Fin 2) (GaloisField p m)) = 2 ^ 3 * 3 ^ 1 := by
      rw [CFSG.SL2MinimalFaithful.card_specialLinearGroup_fin_two, hcard, h3]
      norm_num
    have hsl := isSolvable_of_card_two_three hc
    have hpsl : Group.IsSolvable (PSL2MatrixGroup (GaloisField p m)) :=
      Group.isSolvable_of_surjective (QuotientGroup.mk'_surjective
        (Subgroup.center (Matrix.SpecialLinearGroup (Fin 2) (GaloisField p m))))
    exact Group.isSolvable_of_surjective hσ
  · have h5 : 5 ≤ p ^ m := by
      obtain ⟨k, hk⟩ := hodd
      omega
    have hsimple : IsSimpleGroup (PSL2MatrixGroup (GaloisField p m)) :=
      Matrix.ProjectiveSpecialLinearGroup.rank_two_simple (by omega)
    have hinj := injective_of_surjective_simple σ hσ
    let e : PSL2MatrixGroup (GaloisField p m) ≃* S := MulEquiv.ofBijective σ ⟨hinj, hσ⟩
    have hLie : CFSG.Blueprint.LieModel S .PSL 2 p m :=
      Or.inl ⟨by decide, statedClassicalModel_psl_two_lifted p m (by omega) e.symm⟩
    exact CFSG.Blueprint.lieModel_catalog S _ _ _ _ hLie

theorem psl2_subgroup_dichotomy
    {F : Type} [Field F] [Finite F] {p f : ℕ} [Fact p.Prime]
    (hF : Nat.card F = p ^ f) (H : Subgroup (PSL2MatrixGroup F)) :
    Group.IsSolvable H ∨ Nonempty (H ≃* alternatingGroup (Fin 5)) ∨
      (∃ m, m ∣ f ∧ Nonempty (H ≃* PSL2MatrixGroup (GaloisField p m))) ∨
      (∃ m, 2 * m ∣ f ∧ Nonempty (H ≃* Matrix.ProjGenLinGroup (Fin 2) (GaloisField p m))) := by
  rcases dickson_psl2_subgroup_list hF H with
    ⟨m, -, -, hel⟩ | ⟨z, -, -, hcyc⟩ | ⟨z, hz2, -, ⟨e⟩⟩ | ⟨-, ⟨e⟩⟩ | ⟨-, ⟨e⟩⟩ | ⟨-, ⟨e⟩⟩ |
      ⟨m, t, -, -, -, -, E, C, hEn, hEel, -, hCcyc, -, -, -, -, φ, -, ⟨e⟩⟩ |
      ⟨m, hm, ⟨e⟩⟩ | ⟨m, hm, ⟨e⟩⟩
  · left
    exact Group.isSolvable_of_comm fun a b => hel.toIsMulCommutative.is_comm.comm a b
  · left
    have : CommGroup H := IsCyclic.commGroup
    infer_instance
  · left
    have : NeZero z := ⟨by omega⟩
    have := CFSG.LinearGroups.isSolvable_dihedralGroup z
    exact isSolvable_of_mulEquiv_lifted e
  · left
    have hc : Nat.card (alternatingGroup (Fin 4)) = 2 ^ 2 * 3 ^ 1 := by
      rw [Nat.card_eq_fintype_card, card_alternatingGroup, Fintype.card_fin]
      decide
    have := isSolvable_of_card_two_three hc
    exact isSolvable_of_mulEquiv_lifted e
  · left
    have hc : Nat.card (Equiv.Perm (Fin 4)) = 2 ^ 3 * 3 ^ 1 := by
      rw [Nat.card_eq_fintype_card, Fintype.card_perm, Fintype.card_fin]
      decide
    have := isSolvable_of_card_two_three hc
    exact isSolvable_of_mulEquiv_lifted e
  · exact Or.inr (Or.inl ⟨e⟩)
  · left
    have hE : Group.IsSolvable ↥E :=
      Group.isSolvable_of_comm fun a b => hEel.toIsMulCommutative.is_comm.comm a b
    have hC : Group.IsSolvable ↥C := by
      have : CommGroup ↥C := IsCyclic.commGroup
      infer_instance
    have := isSolvable_semidirectProduct φ
    exact isSolvable_of_mulEquiv_lifted e
  · exact Or.inr (Or.inr (Or.inl ⟨m, hm, ⟨e⟩⟩))
  · exact Or.inr (Or.inr (Or.inr ⟨m, hm, ⟨e⟩⟩))

theorem catalog_of_psl2_subgroup_quotient
    {F : Type} [Field F] [Finite F] {p f : ℕ} [Fact p.Prime]
    (hp : Odd p) (hf : f ≠ 0) (hF : Nat.card F = p ^ f) (Hb : Subgroup (PSL2MatrixGroup F))
    {S : Type} [Group S] [IsSimpleGroup S] (hab : ∃ a b : S, a * b ≠ b * a) (ρ : ↥Hb →* S)
    (hρ : Function.Surjective ρ) : CFSG.Blueprint.Catalog S := by
  have hne : ∀ {m : ℕ}, m ∣ f → m ≠ 0 := fun {m} hm h0 => hf (by
    rw [h0] at hm
    exact zero_dvd_iff.1 hm)
  rcases psl2_subgroup_dichotomy hF Hb with hsolv | hA5 | ⟨m, hm, hPSL⟩ | ⟨m, hm, hPGL⟩
  · exact absurd (Group.isSolvable_of_surjective hρ) (not_isSolvable_of_simple_nonabelian hab)
  ·
    obtain ⟨e⟩ := hA5
    have : IsSimpleGroup (alternatingGroup (Fin 5)) := alternatingGroup.isSimpleGroup (by simp)
    have hs : Function.Surjective (ρ.comp e.symm.toMonoidHom) := hρ.comp e.symm.surjective
    have hinj := injective_of_surjective_simple (ρ.comp e.symm.toMonoidHom) hs
    exact Or.inr (Or.inl ⟨5, le_rfl,
      ⟨(MulEquiv.ofBijective (ρ.comp e.symm.toMonoidHom) ⟨hinj, hs⟩).symm⟩⟩)
  ·
    obtain ⟨e⟩ := hPSL
    exact catalog_of_quotient_psl2 hp (hne hm) hab (ρ.comp e.symm.toMonoidHom)
      (hρ.comp e.symm.surjective)
  ·
    obtain ⟨e⟩ := hPGL
    have hm0 : m ≠ 0 := hne (Dvd.dvd.trans (dvd_mul_left m 2) hm)
    let R₀ : Subgroup (Matrix.ProjGenLinGroup (Fin 2) (GaloisField p m)) :=
      (Matrix.ProjectiveSpecialLinearGroup.toPGL (n := Fin 2) (R := GaloisField p m)).range
    have hoddm : Odd (Nat.card (GaloisField p m)) := by
      rw [GaloisField.card p m hm0]
      exact hp.pow
    have hidx : R₀.index = 2 :=
      pgl2_psl2Range_index_eq_two (GaloisField p m) (isOddPrimePower_card_of_odd hoddm)
    have : R₀.Normal := Subgroup.normal_of_index_eq_two hidx
    let ρ' : Matrix.ProjGenLinGroup (Fin 2) (GaloisField p m) →* S := ρ.comp e.symm.toMonoidHom
    have hρ' : Function.Surjective ρ' := hρ.comp e.symm.surjective
    have hnorm : (R₀.map ρ').Normal := Subgroup.Normal.map inferInstance ρ' hρ'
    rcases hnorm.eq_bot_or_eq_top with h0 | h1
    · exact (not_nonabelian_of_map_eq_bot S R₀ hidx ρ' hρ' h0 hab).elim
    ·
      let σ : PSL2MatrixGroup (GaloisField p m) →* S :=
        ρ'.comp (Matrix.ProjectiveSpecialLinearGroup.toPGL (n := Fin 2) (R := GaloisField p m))
      have hσ : Function.Surjective σ := by
        intro s
        have : s ∈ R₀.map ρ' := by rw [h1]; trivial
        obtain ⟨x, ⟨y, rfl⟩, rfl⟩ := this
        exact ⟨y, rfl⟩
      exact catalog_of_quotient_psl2 hp hm0 hab σ hσ

theorem sl2IsKGroup : SL2IsKGroup := by
  intro F _ _ hodd h3 H N hN hS
  by_cases hab : ∀ a b : H ⧸ N, a * b = b * a
  ·
    have hprime : (Nat.card (H ⧸ N)).Prime := prime_card_of_simple_abelian hab
    have : Fact (Nat.card (H ⧸ N)).Prime := ⟨hprime⟩
    have hcyc : IsCyclic (H ⧸ N) := isCyclic_of_prime_card rfl
    exact Or.inl ⟨Nat.card (H ⧸ N), hprime, ⟨(zmodCyclicMulEquiv hcyc).symm⟩⟩
  · push Not at hab
    let Z := Subgroup.center (Matrix.SpecialLinearGroup (Fin 2) F)
    let π : Matrix.SpecialLinearGroup (Fin 2) F →* PSL2MatrixGroup F := QuotientGroup.mk' Z
    let Hb : Subgroup (PSL2MatrixGroup F) := H.map π
    let ι : ↥H →* ↥Hb := (π.comp H.subtype).codRestrict Hb (fun h => ⟨h, h.2, rfl⟩)
    have hι : Function.Surjective ι := by
      rintro ⟨y, h, hh, rfl⟩
      exact ⟨⟨h, hh⟩, rfl⟩
    have hker : ι.ker ≤ (QuotientGroup.mk' N).ker := by
      intro h hh
      have h1 : π (h : Matrix.SpecialLinearGroup (Fin 2) F) = 1 := by
        have := congrArg Subtype.val (MonoidHom.mem_ker.1 hh)
        exact this
      have hZmem : (h : Matrix.SpecialLinearGroup (Fin 2) F) ∈ Z :=
        (QuotientGroup.eq_one_iff _).1 h1
      have hcen : (QuotientGroup.mk h : H ⧸ N) ∈ Subgroup.center (H ⧸ N) := by
        rw [Subgroup.mem_center_iff]
        intro s
        obtain ⟨h', rfl⟩ := QuotientGroup.mk_surjective s
        rw [← QuotientGroup.mk_mul, ← QuotientGroup.mk_mul]
        congr 1
        apply Subtype.ext
        exact Subgroup.mem_center_iff.1 hZmem (h' : Matrix.SpecialLinearGroup (Fin 2) F)
      exact MonoidHom.mem_ker.2 (center_eq_one_of_simple_nonabelian hab _ hcen)
    let ρ : ↥Hb →* H ⧸ N :=
      MonoidHom.liftOfRightInverse ι (Function.surjInv hι) (Function.rightInverse_surjInv hι)
        ⟨QuotientGroup.mk' N, hker⟩
    have hρι : ∀ h : ↥H, ρ (ι h) = QuotientGroup.mk h := fun h =>
      MonoidHom.liftOfRightInverse_comp_apply ι (Function.surjInv hι)
        (Function.rightInverse_surjInv hι) ⟨QuotientGroup.mk' N, hker⟩ h
    have hρ : Function.Surjective ρ := by
      intro s
      obtain ⟨h, rfl⟩ := QuotientGroup.mk_surjective s
      exact ⟨ι h, hρι h⟩
    obtain ⟨p, f, hp, hpodd, hf, hcard⟩ := isOddPrimePower_card_of_odd hodd
    have : Fact p.Prime := ⟨hp⟩
    exact catalog_of_psl2_subgroup_quotient hpodd (by omega) hcard Hb hab ρ hρ

theorem ii4_aut (h2A7 : II4_2A7) : II4_Aut :=
  ii4_aut_of_kgroup h2A7 sl2IsKGroup

end CFSG.GH74.GLS.IVK.Lifted
