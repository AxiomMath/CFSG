module

public import CFSG.Quasithin.Background.DicksonPerfectPSL2
public import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.PGL2PerfectSubnormal
public import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.PSL2PerfectOfCard
public import CFSG.LocalAnalysis.QuasithinUnique.Ch1.A312ListCore
public import CFSG.LocalAnalysis.QuasithinUnique.Ch1.A312ListFamilies

public section

namespace CFSG.QuasithinUnique.Vol2Native.A312L

open CFSG.Quasithin CFSG.Quasithin.Dickson CFSG.Assembly.LowTwoRank CFSG.Glauberman.Dickson
  CFSG.GorensteinWalter
open CFSG.BenderSuzuki.MatrixGroups

section Dickson

variable {F : Type} [Field F] [Finite F] {p f : ℕ} [Fact p.Prime]

theorem dickson_nonsolvable_cases (hFcard : Nat.card F = p ^ f)
    (H : Subgroup (PSL2MatrixGroup F)) (hns : ¬ Group.IsSolvable H) :
    (Nonempty (H ≃* alternatingGroup (Fin 5)) ∧ (p = 5 ∨ 5 ∣ p ^ (2 * f) - 1)) ∨
      (∃ m : ℕ, m ≠ 0 ∧ m ∣ f ∧ Nonempty (H ≃* PSL2MatrixGroup (GaloisField p m))) ∨
      (∃ m : ℕ, m ≠ 0 ∧ 2 * m ∣ f ∧
        Nonempty (H ≃* Matrix.ProjGenLinGroup (Fin 2) (GaloisField p m))) := by
  rcases huppert_II_8_27_dickson_psl2_subgroup_classification hFcard H with
    h1 | ⟨z, -, -, hcyc⟩ | ⟨z, -, -, ⟨e⟩⟩ | ⟨-, ⟨e⟩⟩ | ⟨-, ⟨e⟩⟩ | ⟨h5, ⟨e⟩⟩ |
      ⟨m, t, -, -, N, C, hN, hNel, -, hC, -, -, hsup⟩ | hPSL | hPGL
  · have := h1.toIsMulCommutative
    exact (hns inferInstance).elim
  · exact (hns inferInstance).elim
  · have := isSolvable_dihedral z
    exact absurd (Group.isSolvable_of_isSolvable_injective (f := e.toMonoidHom) e.injective) hns
  · have := alternatingGroup.isSolvable (α := Fin 4) (by simp)
    exact absurd (Group.isSolvable_of_isSolvable_injective (f := e.toMonoidHom) e.injective) hns
  · have := Equiv.Perm.isSolvable (α := Fin 4) (by simp)
    exact absurd (Group.isSolvable_of_isSolvable_injective (f := e.toMonoidHom) e.injective) hns
  · exact Or.inl ⟨⟨e⟩, h5⟩
  · exfalso
    apply hns
    have := hN
    have hcomm : commutator H ≤ N :=
      Subgroup.Normal.commutator_le_of_self_sup_commutative_eq_top hsup inferInstance
    have hNs : Group.IsSolvable N := by
      have := hNel.toIsMulCommutative
      infer_instance
    have hQs : Group.IsSolvable (H ⧸ N) := by
      have : IsMulCommutative (H ⧸ N) :=
        Subgroup.Normal.quotient_commutative_iff_commutator_le.mpr hcomm
      infer_instance
    exact Group.isSolvable_of_subgroup_quotient N
  · exact Or.inr (Or.inl hPSL)
  · exact Or.inr (Or.inr hPGL)

end Dickson

section Arithmetic

theorem eight_dvd_card_of_isSylowTwoOf {X : Type} [Group X] [Finite X] {T : Subgroup X}
    (hT : CFSG.QuasithinUnique.IsSylowTwoOf T ⊤) (h8 : 8 ∣ Nat.card X) : 8 ∣ Nat.card T := by
  obtain ⟨k, hk⟩ := hT.2.1.exists_card_eq
  have hidx : ¬ 2 ∣ T.index := by
    have := hT.2.2
    rwa [show (T.subgroupOf ⊤).index = T.index from Subgroup.relIndex_top_right _] at this
  have hXS := (Subgroup.card_mul_index T).symm
  rw [hk] at hXS
  rw [hXS] at h8
  have hcop : Nat.Coprime (2 ^ 3) T.index :=
    Nat.Coprime.pow_left 3 ((Nat.Prime.coprime_iff_not_dvd Nat.prime_two).mpr hidx)
  have h8' : 2 ^ 3 ∣ 2 ^ k := hcop.dvd_of_dvd_mul_right (by simpa using h8)
  rw [hk]
  simpa using h8'

theorem not_two_dvd_index_of_le_isSylowTwoOf {X : Type} [Group X] [Finite X] {T M : Subgroup X}
    (hT : CFSG.QuasithinUnique.IsSylowTwoOf T ⊤) (hTM : T ≤ M) : ¬ 2 ∣ M.index := by
  have hidx : ¬ 2 ∣ T.index := by
    have := hT.2.2
    rwa [show (T.subgroupOf ⊤).index = T.index from Subgroup.relIndex_top_right _] at this
  exact fun h => hidx (h.trans (Subgroup.index_dvd_of_le hTM))

variable {p : ℕ} [hp : Fact p.Prime]

theorem odd_of_ne_two' (hp2 : p ≠ 2) : p % 2 = 1 := by
  rcases Nat.Prime.eq_two_or_odd hp.out with h | h
  · exact absurd h hp2
  · exact h

theorem card_psl2_sq {F : Type} [Field F] [Finite F] (hp2 : p ≠ 2) (hF : Nat.card F = p ^ 2) :
    Nat.card (PSL2MatrixGroup F) * 2 = p ^ 2 * (p ^ 4 - 1) := by
  have hodd : Odd p := hp.out.odd_of_ne_two hp2
  have hc := psl2_card_formula F ⟨p, 2, hp.out, hodd, by norm_num, hF⟩
  have h2 : 2 ∣ p ^ 2 * (p ^ 4 - 1) := by
    have h1 : (p ^ 4) % 2 = 1 := by
      rw [Nat.pow_mod, odd_of_ne_two' hp2]
    have : 1 ≤ p ^ 4 := Nat.one_le_pow _ _ hp.out.pos
    exact Dvd.dvd.mul_left (by omega) _
  rw [show Nat.card (PSL2MatrixGroup F) = Nat.card (PSL2 F) from rfl, hc, hF]
  have : p ^ 2 * ((p ^ 2) ^ 2 - 1) = p ^ 2 * (p ^ 4 - 1) := by rw [← pow_mul]
  rw [this]
  exact Nat.div_mul_cancel h2

theorem card_psl2_prime' (hp2 : p ≠ 2) :
    Nat.card (PSL2MatrixGroup (GaloisField p 1)) * 2 = p * (p ^ 2 - 1) := by
  have hodd : Odd p := hp.out.odd_of_ne_two hp2
  have hK : Nat.card (GaloisField p 1) = p ^ 1 := GaloisField.card p 1 one_ne_zero
  have hc := psl2_card_formula (GaloisField p 1) ⟨p, 1, hp.out, hodd, le_rfl, hK⟩
  have h2 : 2 ∣ p * (p ^ 2 - 1) := by
    have h1 : (p ^ 2) % 2 = 1 := by
      rw [Nat.pow_mod, odd_of_ne_two' hp2]
    have : 1 ≤ p ^ 2 := Nat.one_le_pow _ _ hp.out.pos
    exact Dvd.dvd.mul_left (by omega) _
  rw [show Nat.card (PSL2MatrixGroup (GaloisField p 1)) = Nat.card (PSL2 (GaloisField p 1)) from rfl,
    hc, hK, pow_one]
  exact Nat.div_mul_cancel h2

theorem eight_dvd_card_psl2_sq {F : Type} [Field F] [Finite F] (hp2 : p ≠ 2)
    (hF : Nat.card F = p ^ 2) : 8 ∣ Nat.card (PSL2MatrixGroup F) := by
  have h := card_psl2_sq hp2 hF
  have hmod : p ^ 2 % 8 = 1 := by
    have hodd := odd_of_ne_two' hp2
    have h8 : p % 8 = 1 ∨ p % 8 = 3 ∨ p % 8 = 5 ∨ p % 8 = 7 := by omega
    rcases h8 with h8 | h8 | h8 | h8 <;> simp [Nat.pow_mod, h8]
  obtain ⟨a, ha⟩ : ∃ a, p ^ 2 = 8 * a + 1 := ⟨p ^ 2 / 8, by omega⟩
  have h4 : p ^ 4 = (8 * a + 1) ^ 2 := by rw [← ha]; ring
  rw [h4, ha] at h
  have : (8 * a + 1) * ((8 * a + 1) ^ 2 - 1) = 16 * ((8 * a + 1) * (a * (4 * a + 1))) := by
    have : (8 * a + 1) ^ 2 - 1 = 16 * (a * (4 * a + 1)) := by
      have : (8 * a + 1) ^ 2 = 16 * (a * (4 * a + 1)) + 1 := by ring
      omega
    rw [this]
    ring
  rw [this] at h
  exact ⟨(8 * a + 1) * (a * (4 * a + 1)), by omega⟩

end Arithmetic

section PGL

theorem perfectCore_pgl2 {X : Type} [Group X] [Finite X] {M : Subgroup X} {K : Type} [Field K]
    [Finite K] (hK : IsOddPrimePower (Nat.card K)) (hns : ¬ Group.IsSolvable ↥M)
    (φ : ↥M ≃* PGL2 K) : 3 < Nat.card K ∧ Nonempty (↥(perfectCore M) ≃* PSL2 K) := by
  have hNperf : Group.IsPerfect ↥(perfectCore M) :=
    Subgroup.isPerfect_iff.mpr (perfectCore_perfect M)
  have hNne : perfectCore M ≠ ⊥ := fun h => hns ((isSolvable_iff_perfectCore_eq_bot M).mpr h)
  let N' : Subgroup ↥M := (perfectCore M).subgroupOf M
  let eN : ↥N' ≃* ↥(perfectCore M) := Subgroup.subgroupOfEquivOfLe (perfectCore_le M)
  let J : Subgroup (PGL2 K) := N'.map φ.toMonoidHom
  let eJ : ↥N' ≃* ↥J := N'.equivMapOfInjective φ.toMonoidHom φ.injective
  have hJperf : Group.IsPerfect ↥J := by
    have : Group.IsPerfect ↥N' :=
      Group.IsPerfect.ofSurjective (f := eN.symm.toMonoidHom) eN.symm.surjective
    exact Group.IsPerfect.ofSurjective (f := eJ.toMonoidHom) eJ.surjective
  have hJne : J ≠ ⊥ := by
    intro h
    apply hNne
    have hN'bot : N' = ⊥ :=
      Subgroup.map_injective (f := φ.toMonoidHom) φ.injective (by rw [Subgroup.map_bot]; exact h)
    rw [eq_bot_iff]
    intro x hx
    have hxN' : (⟨x, perfectCore_le M hx⟩ : ↥M) ∈ N' := hx
    rw [hN'bot, Subgroup.mem_bot] at hxN'
    have h3 : x = 1 := congrArg Subtype.val hxN'
    rw [h3]
    exact Subgroup.one_mem _
  have hJn : J.Normal := Subgroup.Normal.map (perfectCore_normal M) φ.toMonoidHom φ.surjective
  have : Finite (PGL2 K) := Finite.of_equiv ↥M φ.toEquiv
  obtain ⟨hcard, hJeq⟩ :=
    pgl2_perfect_subnormal_eq_commutator K hK J hJne hJperf hJn.isSubnormal
  let e3 : ↥J ≃* ↥(commutator (PGL2 K)) := MulEquiv.subgroupCongr hJeq
  let e4 : ↥(commutator (PGL2 K)) ≃* PSL2 K :=
    (commutator_mulEquiv_psl2_of_mulEquiv_pgl2_card_gt_three K hK hcard (MulEquiv.refl (PGL2 K))).some
  exact ⟨hcard, ⟨eN.symm.trans (eJ.trans (e3.trans e4))⟩⟩

end PGL

section Main

variable {p : ℕ} [hp : Fact p.Prime]

include hp in
theorem l2psq_psl2
    {F : Type} [Field F] [Finite F] (hp2 : p ≠ 2) (hF : Nat.card F = p ^ 2)
    (hq : CFSG.IsQuasisimple (PSL2MatrixGroup F)) (hmodel : IsPSL 2 p 2 (PSL2MatrixGroup F)) :
    A312For (PSL2MatrixGroup F) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨P₀⟩ := (Sylow.nonempty : Nonempty (Sylow 2 (PSL2MatrixGroup F)))
  have hTsyl := CFSG.QuasithinUnique.isSylowTwoOf_top_of_sylow P₀
  generalize (P₀ : Subgroup (PSL2MatrixGroup F)) = T at hTsyl
  refine A312For.of_sylow T hTsyl fun B hB hBtop => ?_
  have hB' : B ∈ cComp (B ⊔ T) := hB
  have hMne : B ⊔ T ≠ ⊤ := by
    intro htop
    rw [htop] at hB'
    exact hBtop (A321.cComp_eq_top_of_quasisimple hq hB')
  have hMns : ¬ Group.IsSolvable ↥(B ⊔ T) := fun hs =>
    not_isSolvable_of_mem_cComp hB'
      (Group.isSolvable_of_isSolvable_injective
        (f := Subgroup.inclusion (le_of_mem_cComp hB' : B ≤ B ⊔ T))
        (Subgroup.inclusion_injective _))
  have hF1 : Nat.card (GaloisField p 1) = p ^ 1 := GaloisField.card p 1 one_ne_zero
  have hodd : Odd p := hp.out.odd_of_ne_two hp2
  have hK1 : IsOddPrimePower (Nat.card (GaloisField p 1)) := ⟨p, 1, hp.out, hodd, le_rfl, hF1⟩
  have hX := card_psl2_sq hp2 hF
  rcases dickson_nonsolvable_cases (p := p) (f := 2) hF (B ⊔ T) hMns with
    ⟨⟨e⟩, -⟩ | ⟨m, hm0, hm2, ⟨e⟩⟩ | ⟨m, hm0, hm2, ⟨e⟩⟩
  ·
    exfalso
    have h8 := eight_dvd_card_of_isSylowTwoOf hTsyl (eight_dvd_card_psl2_sq hp2 hF)
    have hTM : Nat.card T ∣ Nat.card ↥(B ⊔ T) := Subgroup.card_dvd_of_le le_sup_right
    rw [Nat.card_congr e.toEquiv, card_alt_five] at hTM
    have := h8.trans hTM
    norm_num at this
  · have hm : m = 1 ∨ m = 2 := by
      have := Nat.le_of_dvd (by norm_num) hm2
      omega
    exfalso
    rcases hm with rfl | rfl
    ·
      have hcM : Nat.card ↥(B ⊔ T) * 2 = p * (p ^ 2 - 1) := by
        rw [Nat.card_congr e.toEquiv]
        exact card_psl2_prime' hp2
      have hidx := Subgroup.card_mul_index (B ⊔ T)
      have hodd2 := odd_of_ne_two' (p := p) hp2
      obtain ⟨b, hb⟩ : ∃ b, p ^ 2 = b + 1 := ⟨p ^ 2 - 1, by
        have : 1 ≤ p ^ 2 := Nat.one_le_pow _ _ hp.out.pos
        omega⟩
      have hb' : p ^ 2 - 1 = b := by omega
      have hpb : 0 < p * b := by
        have : 1 < p ^ 2 := by
          have := hp.out.two_le
          nlinarith
        have hbpos : 0 < b := by omega
        exact Nat.mul_pos hp.out.pos hbpos
      have h4 : p ^ 4 = (b + 1) ^ 2 := by rw [← hb]; ring
      rw [h4, hb] at hX
      rw [hb'] at hcM
      have hX' : (b + 1) * ((b + 1) ^ 2 - 1) = (b + 1) * (b * (b + 2)) := by
        have : (b + 1) ^ 2 - 1 = b * (b + 2) := by
          have : (b + 1) ^ 2 = b * (b + 2) + 1 := by ring
          omega
        rw [this]
      rw [hX'] at hX
      have hd : (B ⊔ T).index = p * (b + 2) := by
        refine Nat.eq_of_mul_eq_mul_left hpb ?_
        have : Nat.card ↥(B ⊔ T) * (B ⊔ T).index * 2 = Nat.card (PSL2MatrixGroup F) * 2 := by
          rw [hidx]
        calc p * b * (B ⊔ T).index = (Nat.card ↥(B ⊔ T) * 2) * (B ⊔ T).index := by rw [hcM]
          _ = Nat.card ↥(B ⊔ T) * (B ⊔ T).index * 2 := by ring
          _ = Nat.card (PSL2MatrixGroup F) * 2 := this
          _ = (b + 1) * (b * (b + 2)) := hX
          _ = p * b * (p * (b + 2)) := by
              have : (b + 1) = p ^ 2 := hb.symm
              rw [this]
              ring
      have h2 : 2 ∣ (B ⊔ T).index := by
        rw [hd]
        have : (p ^ 2) % 2 = 1 := by rw [Nat.pow_mod, hodd2]
        exact Dvd.dvd.mul_left (by omega) p
      exact not_two_dvd_index_of_le_isSylowTwoOf hTsyl le_sup_right h2
    ·
      apply hMne
      apply Subgroup.eq_top_of_card_eq
      have hK2 : Nat.card (GaloisField p 2) = p ^ 2 := GaloisField.card p 2 (by norm_num)
      have hcM := card_psl2_sq (F := GaloisField p 2) hp2 hK2
      rw [Nat.card_congr e.toEquiv]
      omega
  ·
    have hm : m = 1 := by
      have := Nat.le_of_dvd (by norm_num) hm2
      omega
    subst hm
    obtain ⟨hcard, ⟨eN⟩⟩ := perfectCore_pgl2 hK1 hMns e
    have hp3 : 3 < p := by rwa [hF1, pow_one] at hcard
    have hS : IsSimpleGroup (PSL2 (GaloisField p 1)) :=
      Matrix.ProjectiveSpecialLinearGroup.rank_two_simple (by omega)
    have hnab : ∃ a b : PSL2 (GaloisField p 1), a * b ≠ b * a := by
      by_contra hcon
      push Not at hcon
      have hsolv : Group.IsSolvable (PSL2 (GaloisField p 1)) :=
        IsSimpleGroup.comm_iff_isSolvable.mp hcon
      have hperf := psl2_isPerfect_of_card_gt_three (GaloisField p 1) hcard
      exact (Group.IsSolvable.commutator_lt_top_of_nontrivial
        (G := PSL2 (GaloisField p 1))).ne (Group.isPerfect_def.mp hperf)
    have hBeq : B = perfectCore (B ⊔ T) :=
      lFamily_eq_perfectCore hB hnab eN.toMonoidHom eN.surjective (by
        have : (eN.toMonoidHom).ker = ⊥ := (MonoidHom.ker_eq_bot_iff _).mpr eN.injective
        rw [this]
        infer_instance)
    have hBiso : ↥B ≃* StatedProj (StatedSL 2 (GaloisField p 1)) :=
      ((MulEquiv.subgroupCongr hBeq).trans eN).trans
        (projectiveSpecialLinearGroupEquivStatedProj 2 (GaloisField p 1))
    have hBmodel : IsPSL 2 p 1 ↥B := by
      refine ⟨⟨hp.out, le_rfl, le_rfl, ?_, ?_⟩, GaloisField p 1, inferInstance, inferInstance,
        hF1, ⟨hBiso⟩⟩
      · intro h
        have := congrArg Prod.snd h
        simp at this
        omega
      · intro h
        have := congrArg Prod.snd h
        simp at this
        omega
    have hLmodel : IsPSL 2 p 2 ↥(⊤ : Subgroup (PSL2MatrixGroup F)) :=
      IsPSL.of_mulEquiv Subgroup.topEquiv.symm hmodel
    iterate 6 right
    left
    left
    exact ⟨p, hp.out, hp3, hBmodel, hLmodel⟩

theorem l2psq : FamL2psq := by
  intro X _ _ p hq hp hp2 hX
  have : Fact p.Prime := ⟨hp⟩
  have hX' := hX
  obtain ⟨-, K, hF, hFin, hcard, ⟨e⟩⟩ := hX
  let e' : X ≃* PSL2MatrixGroup K :=
    e.trans (projectiveSpecialLinearGroupEquivStatedProj 2 K).symm
  exact A312For.of_mulEquiv e'
    (l2psq_psl2 hp2 hcard (CFSG.LocalCores.isQuasisimple_of_mulEquiv e' hq)
      (IsPSL.of_mulEquiv e' hX'))

end Main

end CFSG.QuasithinUnique.Vol2Native.A312L
