module

public import CFSG.LocalAnalysis.GLTheoremA.PartI.I1412
import CFSG.LocalAnalysis.GLTheoremA.S4.Lemma49i
public import CFSG.LocalAnalysis.GLTheoremA.Pump

public section

namespace CFSG.LocalAnalysis.GLTheoremA

open CFSG.Open CFSG.Yardstones.Md0ec50421ce4 CFSG.LocalAnalysis.GLTheoremB
open CFSG.HardMathSupport.Solomon.Coordinator (fixSubgroup mem_fixSubgroup)

@[expose] def KDChevDown (p : ℕ) : Prop :=
  ∀ (S : Type) [Group S] [Finite S], IsSimpleGroup S → (∃ a b : S, a * b ≠ b * a) →
    IsChevSimple p S → ∀ α : MulAut S, α ^ p = 1 →
      ∀ I : Subgroup S, GLAPComponent p (fixSubgroup α) I → IsChevSimple p (PSimple p I)

@[expose] def KDCharP (p : ℕ) : Prop :=
  ∀ (d : TauCeti.ValidLieTypeIndex), d.1.characteristic = p →
    ∀ u : (TauCeti.CFSGIndex.lie d).Group, orderOf u = p →
      GLAPLayer p (Subgroup.centralizer ({u} : Set (TauCeti.CFSGIndex.lie d).Group)) = ⊥

@[expose] def KDOutChev (p : ℕ) : Prop :=
  ∀ (d : TauCeti.ValidLieTypeIndex), d.1.characteristic = p →
    ∀ α : MulAut (TauCeti.CFSGIndex.lie d).Group, orderOf α = p →
      α ∉ (MulAut.conj : (TauCeti.CFSGIndex.lie d).Group →* _).range →
      ∀ I : Subgroup (TauCeti.CFSGIndex.lie d).Group, GLAPComponent p (fixSubgroup α) I →
        IsChevSimple p (PSimple p I)

@[expose] def KDLevelTwo (p : ℕ) : Prop :=
  ∀ (S : Type) [Group S] [Finite S], IsSimpleGroup S → (∃ a b : S, a * b ≠ b * a) →
    catalogIs S (k2 p) → DownLe p 2 S

@[expose] def KDLevelThree : Prop :=
  ∀ (S : Type) [Group S] [Finite S], IsSimpleGroup S → (∃ a b : S, a * b ≠ b * a) →
    catalogIs S (k3 3) → DownLe 3 3 S

@[expose] def KDRankTwoDown : Prop :=
  (∀ (q : TauCeti.PrimePower) (hv : (TauCeti.LieTypeIndex.A 1 q).Valid), ¬ 3 ∣ q.card →
      DownLe 3 2 (TauCeti.CFSGIndex.lie ⟨.A 1 q, hv⟩).Group) ∧
  (∀ (q : TauCeti.PrimePower) (hv : (TauCeti.LieTypeIndex.A 2 q).Valid), q.card % 3 = 1 →
      DownLe 3 (if q.p = 2 then 2 else 3) (TauCeti.CFSGIndex.lie ⟨.A 2 q, hv⟩).Group) ∧
  (∀ (q : TauCeti.PrimePower) (hv : (TauCeti.LieTypeIndex.twistedA 2 q).Valid), q.card % 3 = 2 →
      DownLe 3 (if q.p = 2 then 2 else 3) (TauCeti.CFSGIndex.lie ⟨.twistedA 2 q, hv⟩).Group)

@[expose] def KDAltDown : Prop :=
  ∀ (n : ℕ) (p : ℕ), 5 ≤ n → p.Prime → p ≠ 2 → ∀ α : MulAut (alternatingGroup (Fin n)),
    α ^ p = 1 → α ≠ 1 → ∀ I : Subgroup (alternatingGroup (Fin n)),
      GLAPComponent p (fixSubgroup α) I →
        ∃ m : ℕ, max 5 p ≤ m ∧ m + p ≤ n ∧ Nonempty (PSimple p I ≃* alternatingGroup (Fin m))

@[expose] def KDLevelFinite (p : ℕ) : Prop :=
  ∀ i : TauCeti.CFSGIndex,
    (p = 3 → ∀ (d : TauCeti.ValidLieTypeIndex) (q : TauCeti.PrimePower), i = .lie d →
      d.1 ≠ .A 1 q ∧ d.1 ≠ .A 2 q ∧ d.1 ≠ .twistedA 2 q) →
    (∀ n h, i ≠ .alternating n h) →
    (k2 p i → DownLe p 2 i.Group) ∧ (k3 p i → DownLe p 3 i.Group)

private theorem i1412L_kLevel_le_four (p : ℕ) (S : Type) [Group S] : kLevel p S ≤ 4 := by
  unfold kLevel
  split_ifs <;> omega

private theorem i1412L_kLevel_eq_one {p : ℕ} {S : Type} [Group S] (h : IsChevSimple p S) :
    kLevel p S = 1 := by
  unfold kLevel
  rw [if_pos h]

private theorem i1412L_kLevel_le_one {p : ℕ} {S : Type} [Group S] (h : IsChevSimple p S) :
    kLevel p S ≤ 1 :=
  (i1412L_kLevel_eq_one h).le

private theorem i1412L_isChev_of_kLevel_le_one {p : ℕ} {S : Type} [Group S]
    (h : kLevel p S ≤ 1) : IsChevSimple p S := by
  by_contra hne
  unfold kLevel at h
  rw [if_neg hne] at h
  split_ifs at h <;> omega

private theorem i1412L_kLevel_le_two {p : ℕ} {S : Type} [Group S] (h : catalogIs S (k2 p)) :
    kLevel p S ≤ 2 := by
  unfold kLevel
  split_ifs <;> first | omega | exact absurd h ‹_›

private theorem i1412L_kLevel_le_three {p : ℕ} {S : Type} [Group S] (h : catalogIs S (k3 p)) :
    kLevel p S ≤ 3 := by
  unfold kLevel
  split_ifs <;> first | omega | exact absurd h ‹_›

private theorem i1412L_fixSubgroup_one {K : Type*} [Group K] :
    fixSubgroup (1 : MulAut K) = ⊤ := by
  ext x
  rw [mem_fixSubgroup]
  simp

private theorem i1412L_nonab_of_mulEquiv {S T : Type} [Group S] [Group T] (e : S ≃* T)
    (h : ∃ a b : S, a * b ≠ b * a) : ∃ a b : T, a * b ≠ b * a := by
  obtain ⟨a, b, hab⟩ := h
  refine ⟨e a, e b, fun h' => hab (e.injective ?_)⟩
  rw [map_mul, map_mul]
  exact h'

private theorem i1412L_center_eq_bot {T : Type} [Group T] [IsSimpleGroup T]
    (hnc : ∃ a b : T, a * b ≠ b * a) : Subgroup.center T = ⊥ := by
  rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal (Subgroup.center T) with h | h
  · exact h
  · exfalso
    obtain ⟨a, b, hab⟩ := hnc
    have ha : a ∈ Subgroup.center T := by
      rw [h]
      exact Subgroup.mem_top a
    exact hab ((Subgroup.mem_center_iff.1 ha b).symm)

private theorem i1412L_isSubnormal_top {T : Type} [Group T] [IsSimpleGroup T] {H K : Subgroup T}
    (h : IsSubnormal H K) : K = ⊤ → H = ⊥ ∨ H = ⊤ := by
  induction h with
  | refl H => intro hK; exact Or.inr hK
  | @step H M K hle hn _ ih =>
    intro hK
    rcases ih hK with hM | hM
    · exact Or.inl (le_bot_iff.1 (hM ▸ hle))
    · subst hM
      haveI : H.Normal :=
        ⟨fun n hn' g => (Subgroup.normal_subgroupOf_iff le_top).1 hn n g hn' (Subgroup.mem_top g)⟩
      exact IsSimpleGroup.eq_bot_or_eq_top_of_normal H

private theorem i1412L_pSimple_top_equiv {p : ℕ} (hp : p.Prime) {T : Type} [Group T] [Finite T]
    [IsSimpleGroup T] (hnc : ∃ a b : T, a * b ≠ b * a) {I : Subgroup T}
    (hI : GLAPComponent p (⊤ : Subgroup T) I) : Nonempty (PSimple p I ≃* T) := by
  have hIeq : I = ⊤ := by
    rcases i1412L_isSubnormal_top hI.2.1 rfl with h | h
    · exact absurd h (glaPComponent_ne_bot' hI)
    · exact h
  subst hIeq
  have hq : CFSG.Open.IsQuasisimple (PQuot p (⊤ : Subgroup T)) :=
    isQuasisimple_pQuot_of_glaPComponent hp hI
  have hnt : Nontrivial (↥(⊤ : Subgroup T) ⧸ GLAPPrimeCore p ↥(⊤ : Subgroup T)) := by
    haveI : Nontrivial (PQuot p (⊤ : Subgroup T) ⧸ Subgroup.center (PQuot p (⊤ : Subgroup T))) :=
      hq.2.toNontrivial
    exact (QuotientGroup.mk'_surjective
      (Subgroup.center (PQuot p (⊤ : Subgroup T)))).nontrivial
  have hOb : GLAPPrimeCore p ↥(⊤ : Subgroup T) = ⊥ := by
    let ψ : ↥(⊤ : Subgroup T) ≃* T := Subgroup.topEquiv
    haveI : ((GLAPPrimeCore p ↥(⊤ : Subgroup T)).map ψ.toMonoidHom).Normal :=
      Subgroup.Normal.map (GLAPPrimeCore.normal p _) ψ.toMonoidHom ψ.surjective
    rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal
        ((GLAPPrimeCore p ↥(⊤ : Subgroup T)).map ψ.toMonoidHom) with h | h
    · exact (Subgroup.map_eq_bot_iff_of_injective _ ψ.injective).1 h
    · exfalso
      have htop : GLAPPrimeCore p ↥(⊤ : Subgroup T) = ⊤ := by
        apply Subgroup.map_injective (f := ψ.toMonoidHom) ψ.injective
        rw [h, Subgroup.map_top_of_surjective _ ψ.surjective]
      obtain ⟨a, b, hab⟩ := exists_pair_ne (↥(⊤ : Subgroup T) ⧸ GLAPPrimeCore p ↥(⊤ : Subgroup T))
      apply hab
      obtain ⟨x, rfl⟩ := QuotientGroup.mk_surjective a
      obtain ⟨y, rfl⟩ := QuotientGroup.mk_surjective b
      rw [QuotientGroup.eq, htop]
      exact Subgroup.mem_top _
  have hZtop : Subgroup.center ↥(⊤ : Subgroup T) = ⊥ := by
    have h1 := Subgroup.map_center_eq (Subgroup.topEquiv : ↥(⊤ : Subgroup T) ≃* T)
    rw [i1412L_center_eq_bot hnc] at h1
    exact (Subgroup.map_eq_bot_iff_of_injective _ Subgroup.topEquiv.injective).1 h1
  let e1 : PQuot p (⊤ : Subgroup T) ≃* ↥(⊤ : Subgroup T) :=
    (QuotientGroup.quotientMulEquivOfEq hOb).trans QuotientGroup.quotientBot
  let e2 : PSimple p (⊤ : Subgroup T) ≃*
      (↥(⊤ : Subgroup T) ⧸ Subgroup.center ↥(⊤ : Subgroup T)) :=
    QuotientGroup.congr _ _ e1 (Subgroup.map_center_eq e1)
  let e3 : (↥(⊤ : Subgroup T) ⧸ Subgroup.center ↥(⊤ : Subgroup T)) ≃* ↥(⊤ : Subgroup T) :=
    (QuotientGroup.quotientMulEquivOfEq hZtop).trans QuotientGroup.quotientBot
  exact ⟨e2.trans (e3.trans Subgroup.topEquiv)⟩

private theorem i1412L_downLe_one_lie {p : ℕ} (hp : p.Prime) (hC : KDCharP p) (hO : KDOutChev p)
    (d : TauCeti.ValidLieTypeIndex) (hd : d.1.characteristic = p)
    [IsSimpleGroup (TauCeti.CFSGIndex.lie d).Group] [Finite (TauCeti.CFSGIndex.lie d).Group]
    (hnc : ∃ a b : (TauCeti.CFSGIndex.lie d).Group, a * b ≠ b * a) :
    DownLe p 1 (TauCeti.CFSGIndex.lie d).Group := by
  haveI : Fact p.Prime := ⟨hp⟩
  intro β hβ J hJ
  by_cases hβ1 : β = 1
  · subst hβ1
    rw [i1412L_fixSubgroup_one] at hJ
    obtain ⟨f⟩ := i1412L_pSimple_top_equiv hp hnc hJ
    have hT : IsChevSimple p (TauCeti.CFSGIndex.lie d).Group :=
      Or.inl ⟨TauCeti.CFSGIndex.lie d, hd, ⟨MulEquiv.refl _⟩⟩
    exact (kLevel_congr p f).trans_le (i1412L_kLevel_le_one hT)
  · have hord : orderOf β = p := orderOf_eq_prime hβ hβ1
    by_cases hin : β ∈ (MulAut.conj : (TauCeti.CFSGIndex.lie d).Group →* _).range
    · obtain ⟨u, rfl⟩ := hin
      exfalso
      have hu1 : u ≠ 1 := by
        rintro rfl
        exact hβ1 (map_one _)
      have hup : u ^ p = 1 := by
        have h1 : MulAut.conj (u ^ p) = 1 := by
          rw [map_pow]
          exact hβ
        have hcen : u ^ p ∈ Subgroup.center (TauCeti.CFSGIndex.lie d).Group := by
          rw [Subgroup.mem_center_iff]
          intro g
          have hg := DFunLike.congr_fun h1 g
          rw [MulAut.conj_apply, MulAut.one_apply] at hg
          exact (mul_inv_eq_iff_eq_mul.1 hg).symm
        rw [i1412L_center_eq_bot hnc, Subgroup.mem_bot] at hcen
        exact hcen
      have hord' : orderOf u = p := orderOf_eq_prime hup hu1
      have hfix : fixSubgroup (MulAut.conj u) =
          Subgroup.centralizer ({u} : Set (TauCeti.CFSGIndex.lie d).Group) := by
        ext x
        rw [mem_fixSubgroup, Subgroup.mem_centralizer_singleton_iff, MulAut.conj_apply,
          mul_inv_eq_iff_eq_mul]
        exact eq_comm
      rw [hfix] at hJ
      have hle : J ≤ GLAPLayer p
          (Subgroup.centralizer ({u} : Set (TauCeti.CFSGIndex.lie d).Group)) := le_sSup hJ
      rw [hC d hd u hord', le_bot_iff] at hle
      exact glaPComponent_ne_bot' hJ hle
    · exact i1412L_kLevel_le_one (hO d hd β hord hin J hJ)

private theorem i1412L_p_ne_two_of_card_mod_two {q : TauCeti.PrimePower} (h : q.card % 2 = 1) :
    q.p ≠ 2 := by
  intro h2
  have hd : 2 ∣ q.card := by
    rw [TauCeti.PrimePower.card_def, h2]
    exact dvd_pow_self 2 (Nat.pos_iff_ne_zero.1 q.exponent_pos)
  omega

private theorem i1412L_card_mod_three_even {q : TauCeti.PrimePower} (h2 : q.p = 2)
    (he : Even q.exponent) : q.card % 3 = 1 := by
  obtain ⟨k, hk⟩ := he
  rw [TauCeti.PrimePower.card_def, h2, hk, ← two_mul, pow_mul, Nat.pow_mod]
  norm_num

private theorem i1412L_card_mod_three_odd {q : TauCeti.PrimePower} (h2 : q.p = 2)
    (ho : Odd q.exponent) : q.card % 3 = 2 := by
  obtain ⟨k, hk⟩ := ho
  rw [TauCeti.PrimePower.card_def, h2, hk, pow_succ, pow_mul, Nat.mul_mod, Nat.pow_mod]
  norm_num

private theorem i1412L_k3Lie_cases {ld : TauCeti.LieTypeIndex} (h : k3Lie ld) :
    (∃ q : TauCeti.PrimePower, ld = .A 2 q ∧ q.card % 6 = 1) ∨
      (∃ q : TauCeti.PrimePower, ld = .twistedA 2 q ∧ q.card % 6 = 5) := by
  cases ld with
  | A n q =>
    rcases n with _ | _ | _ | n
    · exact (show False from h).elim
    · exact (show False from h).elim
    · exact Or.inl ⟨q, rfl, h⟩
    · exact (show False from h).elim
  | twistedA n q =>
    rcases n with _ | _ | _ | n
    · exact (show False from h).elim
    · exact (show False from h).elim
    · exact Or.inr ⟨q, rfl, h⟩
    · exact (show False from h).elim
  | _ => exact (show False from h).elim

private theorem i1412L_downLe_alt {p j n : ℕ} (hp : p.Prime) (hp2 : p ≠ 2) (hA : KDAltDown)
    (hnc : ∃ a b : alternatingGroup (Fin n), a * b ≠ b * a)
    [IsSimpleGroup (alternatingGroup (Fin n))] [Finite (alternatingGroup (Fin n))] (hn : 5 ≤ n)
    (hkn : kLevel p (alternatingGroup (Fin n)) ≤ j)
    (hm : ∀ m : ℕ, 5 ≤ m → m + p ≤ n → kLevel p (alternatingGroup (Fin m)) ≤ j) :
    DownLe p j (alternatingGroup (Fin n)) := by
  intro α hα I hI
  by_cases hα1 : α = 1
  · subst hα1
    rw [i1412L_fixSubgroup_one] at hI
    obtain ⟨f⟩ := i1412L_pSimple_top_equiv hp hnc hI
    exact (kLevel_congr p f).trans_le hkn
  · obtain ⟨m, hm5, hmn, ⟨f⟩⟩ := hA n p hn hp hp2 α hα hα1 I hI
    exact (kLevel_congr p f).trans_le (hm m (le_trans (le_max_left 5 p) hm5) hmn)

theorem kdLevel_of {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2) (h1 : KDChevDown p)
    (h2 : KDLevelTwo p) (h3 : KDLevelThree) : KDLevel p := by
  intro S _ _ hS hnc hcat
  unfold kLevel
  split_ifs with hA hB hC
  · intro α hα I hI
    exact i1412L_kLevel_le_one (h1 S hS hnc hA α hα I hI)
  · exact h2 S hS hnc hB
  · have hp3 : p = 3 := by
      obtain ⟨i, hi, -⟩ := hC
      cases i with
      | cyclic q hq => exact (show False from hi).elim
      | alternating n hn => exact hi.1
      | lie d => exact hi.1
      | sporadic s => exact hi.1
    subst hp3
    exact h3 S hS hnc hC
  · intro α _ I _
    exact i1412L_kLevel_le_four p _

theorem kdChevDown_of {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2) (hC : KDCharP p) (hO : KDOutChev p)
    (hamb : ∀ i : TauCeti.CFSGIndex, ambiguousChev p i → DownLe p 1 i.Group) :
    KDChevDown p := by
  intro S _ _ hS hnc hCS α hα I hI
  have hD : DownLe p 1 S := by
    rcases hCS with ⟨i, hi, ⟨e⟩⟩ | ⟨i, hi, ⟨e⟩⟩
    · cases i with
      | cyclic q hq => exact (show False from hi).elim
      | alternating n hn => exact (show False from hi).elim
      | sporadic s => exact (show False from hi).elim
      | lie d =>
        have hd : d.1.characteristic = p := hi
        haveI : IsSimpleGroup (TauCeti.CFSGIndex.lie d).Group := e.symm.isSimpleGroup
        haveI : Finite (TauCeti.CFSGIndex.lie d).Group := Finite.of_equiv S e.toEquiv
        exact downLe_of_mulEquiv e.symm
          (i1412L_downLe_one_lie hp hC hO d hd (i1412L_nonab_of_mulEquiv e hnc))
    · exact downLe_of_mulEquiv e.symm (hamb i hi)
  exact i1412L_isChev_of_kLevel_le_one (hD α hα I hI)

theorem kdLevelTwo_of {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2) (hF : KDRankTwoDown)
    (hA : KDAltDown) (hfin : KDLevelFinite p) : KDLevelTwo p := by
  intro S _ _ hS hnc hk2
  obtain ⟨i, hi, ⟨e⟩⟩ := hk2
  refine downLe_of_mulEquiv e.symm ?_
  cases i with
  | cyclic q hq => exact (show False from hi).elim
  | alternating n hn =>
    have hk : (p = 3 ∧ (n = 5 ∨ n = 9)) ∨ (p = 7 ∧ n = 7) := hi
    haveI : IsSimpleGroup (alternatingGroup (Fin n)) := e.symm.isSimpleGroup
    haveI : Finite (alternatingGroup (Fin n)) := Finite.of_equiv S e.toEquiv
    have hkn : kLevel p (alternatingGroup (Fin n)) ≤ 2 :=
      i1412L_kLevel_le_two ⟨TauCeti.CFSGIndex.alternating n hn, hi, ⟨MulEquiv.refl _⟩⟩
    refine i1412L_downLe_alt hp hp2 hA (i1412L_nonab_of_mulEquiv e hnc) hn hkn ?_
    intro m hm5 hmn
    rcases hk with ⟨rfl, rfl | rfl⟩ | ⟨rfl, rfl⟩
    · omega
    · rcases (show m = 5 ∨ m = 6 by omega) with rfl | rfl
      · exact i1412L_kLevel_le_two ⟨TauCeti.CFSGIndex.alternating 5 (by norm_num),
          by simp [k2], ⟨MulEquiv.refl _⟩⟩
      · have h6 : kLevel 3 (alternatingGroup (Fin 6)) ≤ 1 :=
          i1412L_kLevel_le_one (Or.inr ⟨TauCeti.CFSGIndex.alternating 6 (by norm_num),
            by simp [ambiguousChev], ⟨MulEquiv.refl _⟩⟩)
        exact h6.trans (by norm_num)
    · omega
  | lie d =>
    obtain ⟨ld, hv⟩ := d
    by_cases hf : ∃ q : TauCeti.PrimePower,
        ld = .A 1 q ∨ ld = .A 2 q ∨ ld = .twistedA 2 q
    · obtain ⟨q, hq | hq | hq⟩ := hf
      · subst hq
        obtain ⟨rfl, hnd⟩ : p = 3 ∧ ¬ 3 ∣ q.card := hi
        exact hF.1 q hv hnd
      · subst hq
        rcases (show (p = 3 ∧ q.p = 2 ∧ Even q.exponent) ∨ (p = 13 ∧ q.card = 3) from hi) with
          ⟨rfl, hq2, hev⟩ | ⟨rfl, hc⟩
        · have h := hF.2.1 q hv (i1412L_card_mod_three_even hq2 hev)
          rwa [if_pos hq2] at h
        · exact (hfin (TauCeti.CFSGIndex.lie ⟨.A 2 q, hv⟩)
            (fun h3 => by norm_num at h3) (fun n h h' => by cases h')).1 hi
      · subst hq
        obtain ⟨rfl, hq2, hodd, -⟩ : p = 3 ∧ q.p = 2 ∧ Odd q.exponent ∧ 1 < q.exponent := hi
        have h := hF.2.2 q hv (i1412L_card_mod_three_odd hq2 hodd)
        rwa [if_pos hq2] at h
    · exact (hfin (TauCeti.CFSGIndex.lie ⟨ld, hv⟩)
        (fun _ d' q h => by
          cases h
          exact ⟨fun h' => hf ⟨q, Or.inl h'⟩, fun h' => hf ⟨q, Or.inr (Or.inl h')⟩,
            fun h' => hf ⟨q, Or.inr (Or.inr h')⟩⟩)
        (fun n h h' => by cases h')).1 hi
  | sporadic s =>
    exact (hfin (TauCeti.CFSGIndex.sporadic s) (fun _ d' q h => by cases h)
      (fun n h h' => by cases h')).1 hi

theorem kdLevelThree_of (hF : KDRankTwoDown) (hA : KDAltDown) (hfin : KDLevelFinite 3) :
    KDLevelThree := by
  have hp3 : Nat.Prime 3 := Nat.prime_three
  intro S _ _ hS hnc hk3
  obtain ⟨i, hi, ⟨e⟩⟩ := hk3
  refine downLe_of_mulEquiv e.symm ?_
  cases i with
  | cyclic q hq => exact (show False from hi).elim
  | alternating n hn =>
    have hk : n = 7 ∨ n = 10 := hi.2
    haveI : IsSimpleGroup (alternatingGroup (Fin n)) := e.symm.isSimpleGroup
    haveI : Finite (alternatingGroup (Fin n)) := Finite.of_equiv S e.toEquiv
    have hkn : kLevel 3 (alternatingGroup (Fin n)) ≤ 3 :=
      i1412L_kLevel_le_three ⟨TauCeti.CFSGIndex.alternating n hn, hi, ⟨MulEquiv.refl _⟩⟩
    refine i1412L_downLe_alt hp3 (by norm_num) hA (i1412L_nonab_of_mulEquiv e hnc) hn hkn ?_
    intro m hm5 hmn
    rcases hk with rfl | rfl
    · omega
    · rcases (show m = 5 ∨ m = 6 ∨ m = 7 by omega) with rfl | rfl | rfl
      · have h5 : kLevel 3 (alternatingGroup (Fin 5)) ≤ 2 :=
          i1412L_kLevel_le_two ⟨TauCeti.CFSGIndex.alternating 5 (by norm_num),
            by simp [k2], ⟨MulEquiv.refl _⟩⟩
        exact h5.trans (by norm_num)
      · have h6 : kLevel 3 (alternatingGroup (Fin 6)) ≤ 1 :=
          i1412L_kLevel_le_one (Or.inr ⟨TauCeti.CFSGIndex.alternating 6 (by norm_num),
            by simp [ambiguousChev], ⟨MulEquiv.refl _⟩⟩)
        exact h6.trans (by norm_num)
      · exact i1412L_kLevel_le_three ⟨TauCeti.CFSGIndex.alternating 7 (by norm_num),
          by simp [k3], ⟨MulEquiv.refl _⟩⟩
  | lie d =>
    obtain ⟨ld, hv⟩ := d
    have hk : k3Lie ld := hi.2
    rcases i1412L_k3Lie_cases hk with ⟨q, rfl, hq⟩ | ⟨q, rfl, hq⟩
    · have hq2 : q.p ≠ 2 := i1412L_p_ne_two_of_card_mod_two (by omega)
      have h := hF.2.1 q hv (by omega)
      rwa [if_neg hq2] at h
    · have hq2 : q.p ≠ 2 := i1412L_p_ne_two_of_card_mod_two (by omega)
      have h := hF.2.2 q hv (by omega)
      rwa [if_neg hq2] at h
  | sporadic s =>
    exact (hfin (TauCeti.CFSGIndex.sporadic s) (fun _ d' q h => by cases h)
      (fun n h h' => by cases h')).2 hi

end CFSG.LocalAnalysis.GLTheoremA
