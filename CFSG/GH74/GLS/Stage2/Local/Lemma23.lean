module

public import CFSG.GH74.GLS.Stage2.Local.Bar
public import CFSG.GH74.GLS.Stage1.Thm6.Prod.Transport
public import CFSG.GH74.GLS.Stage2.Local.Basic

public section

namespace CFSG.GH74.GLS.Stage2.Local

open Subgroup CFSG CFSG.GH74 CFSG.GH74.GLS CFSG.Blueprint CFSG.Assembly.LowTwoRank
  CFSG.GH74.GLS.Stage12 CFSG.GH74.GLS.Stage1.Thm6.Prod
open scoped commutatorElement

section Lift2

variable {X Y : Type*} [Group X] [Group Y]

theorem mem_of_twoElt_of_map_mem [Finite X] (f : X →* Y) (N : Subgroup X) [N.Normal] {x : X}
    (hx : ∃ a : ℕ, orderOf x = 2 ^ a) (hker : Odd (Nat.card f.ker)) (h : f x ∈ N.map f) :
    x ∈ N := by
  obtain ⟨n, hn, hfn⟩ := h
  have hxn : x * n⁻¹ ∈ f.ker := by
    rw [MonoidHom.mem_ker, map_mul, map_inv, hfn, mul_inv_cancel]
  have hod : Odd (orderOf (x * n⁻¹)) := by
    have h1 : orderOf (⟨x * n⁻¹, hxn⟩ : f.ker) ∣ Nat.card f.ker := orderOf_dvd_natCard _
    rw [Subgroup.orderOf_mk] at h1
    exact Odd.of_dvd_nat hker h1
  have hmk : (QuotientGroup.mk x : X ⧸ N) = QuotientGroup.mk (x * n⁻¹) := by
    rw [QuotientGroup.eq]
    simpa using N.inv_mem hn
  have hd1 : orderOf (QuotientGroup.mk x : X ⧸ N) ∣ orderOf x :=
    orderOf_map_dvd (QuotientGroup.mk' N) x
  have hd2 : orderOf (QuotientGroup.mk x : X ⧸ N) ∣ orderOf (x * n⁻¹) := by
    rw [hmk]
    exact orderOf_map_dvd (QuotientGroup.mk' N) (x * n⁻¹)
  obtain ⟨a, hax⟩ := hx
  rw [hax] at hd1
  obtain ⟨i, -, hi⟩ := (Nat.dvd_prime_pow Nat.prime_two).mp hd1
  have hodd : Odd (orderOf (QuotientGroup.mk x : X ⧸ N)) := Odd.of_dvd_nat hod hd2
  have hi0 : i = 0 := by
    by_contra hne
    rw [hi] at hodd
    have h2 : Odd 2 := (Nat.odd_pow_iff hne).mp hodd
    exact absurd h2 (by decide)
  rw [hi0, pow_zero, orderOf_eq_one_iff] at hi
  exact (QuotientGroup.eq_one_iff x).mp hi

end Lift2

section L23

variable {G : Type} [Group G] [Finite G] {z : G} {k : Kind} {S : Subgroup G}

omit [Finite G] in
theorem LC_subgroupOf (z : G) :
    (LC z).subgroupOf (Cen z) = oPrimePResidual 2 ↥(Cen z) ⊓ (InnerE z).comap (toBar z) :=
  Subgroup.comap_map_eq_self_of_injective (Cen z).subtype_injective _

theorem oPrimePResidual_Cen_normal (z : G) : (oPrimePResidual 2 ↥(Cen z)).Normal := by
  constructor
  intro n hn g
  have h := map_oPrimePResidual (X := ↥(Cen z)) (Y := ↥(Cen z))
    (MulAut.conj g).toMonoidHom (MulAut.conj g).surjective Nat.prime_two
  have h1 : (MulAut.conj g).toMonoidHom n ∈
      (oPrimePResidual 2 ↥(Cen z)).map (MulAut.conj g).toMonoidHom := ⟨n, hn, rfl⟩
  rw [h] at h1
  simpa using h1

theorem mem_LC_of_toBar_mem (z : G) {s : G} (hs : s ∈ Cen z) (h2 : ∃ a : ℕ, orderOf s = 2 ^ a)
    (h : toBar z ⟨s, hs⟩ ∈ LBar z) : s ∈ LC z := by
  have hN := oPrimePResidual_Cen_normal z
  unfold LBar barOf at h
  rw [LC_subgroupOf] at h
  obtain ⟨c, hc, hcs⟩ := h
  have h1 : toBar z ⟨s, hs⟩ ∈ (oPrimePResidual 2 ↥(Cen z)).map (toBar z) := ⟨c, hc.1, hcs⟩
  have h3 := mem_of_twoElt_of_map_mem (toBar z) (oPrimePResidual 2 ↥(Cen z)) (x := ⟨s, hs⟩)
    (by rwa [Subgroup.orderOf_mk]) (odd_card_ker_toBar z) h1
  have h4 : (⟨s, hs⟩ : ↥(Cen z)) ∈ (LC z).subgroupOf (Cen z) := by
    rw [LC_subgroupOf]
    refine ⟨h3, ?_⟩
    show toBar z ⟨s, hs⟩ ∈ InnerE z
    rw [← hcs]
    exact hc.2
  exact h4

theorem orderOf_mem_S (h : Stage2Ctx G z k S) {s : G} (hs : s ∈ S) :
    ∃ a : ℕ, orderOf s = 2 ^ a := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨a, ha⟩ := (IsPGroup.iff_orderOf (p := 2) (G := ↥S)).mp h.sylow.isPGroup ⟨s, hs⟩
  exact ⟨a, by rw [Subgroup.orderOf_mk] at ha; exact ha⟩

theorem isPGroup_quotient_of_oResidual_le' {X : Type*} [Group X] [Finite X] {p : ℕ}
    [hp : Fact p.Prime] (L : Subgroup X) [L.Normal] (hL : oResidual p X ≤ L) :
    IsPGroup p (X ⧸ L) := by
  intro q
  obtain ⟨x, rfl⟩ := QuotientGroup.mk_surjective q
  obtain ⟨a, m, hm, hord⟩ :=
    Nat.exists_eq_pow_mul_and_not_dvd (orderOf_pos x).ne' p hp.out.one_lt.ne'
  refine ⟨a, ?_⟩
  rw [← QuotientGroup.mk_pow, QuotientGroup.eq_one_iff]
  apply hL
  apply Subgroup.subset_closure
  change Nat.Coprime (orderOf (x ^ p ^ a)) p
  rw [orderOf_pow_of_dvd (pow_ne_zero a hp.out.ne_zero) (Dvd.intro _ hord.symm), hord,
    Nat.mul_div_cancel_left m (pow_pos hp.out.pos a)]
  exact (Nat.coprime_comm.mp ((Nat.Prime.coprime_iff_not_dvd hp.out).mpr hm))

theorem LBar_normal (z : G) : (LBar z).Normal := by
  unfold LBar barOf
  have := Stage1.Thm6.Prod.LC_normal z
  exact Subgroup.Normal.map inferInstance (toBar z) (toBar_surjective z)

theorem oResidual_perm3_ne_top : oResidual 2 (Equiv.Perm (Fin 3)) ≠ ⊤ := by
  intro h
  have hle : oResidual 2 (Equiv.Perm (Fin 3)) ≤ (Equiv.Perm.sign : Equiv.Perm (Fin 3) →* ℤˣ).ker := by
    rw [oResidual, Subgroup.closure_le]
    intro x hx
    have hodd : Odd (orderOf x) := Nat.coprime_two_right.mp hx
    show Equiv.Perm.sign x = 1
    have h1 : (Equiv.Perm.sign x) ^ orderOf x = 1 := by
      rw [← map_pow, pow_orderOf_eq_one, map_one]
    rcases Int.units_eq_one_or (Equiv.Perm.sign x) with h2 | h2
    · exact h2
    · rw [h2, hodd.neg_one_pow] at h1
      exact absurd h1 (by decide)
  rw [h] at hle
  have h3 : Equiv.Perm.sign (Equiv.swap (0 : Fin 3) 1) = 1 := hle (Subgroup.mem_top _)
  rw [Equiv.Perm.sign_swap (by decide)] at h3
  exact absurd h3 (by decide)

theorem map_eq_top_of_isPGroup_of_odd_index {X Q : Type*} [Group X] [Finite X] [Group Q] [Finite Q]
    (π : X →* Q) (hπ : Function.Surjective π) (hQ : IsPGroup 2 Q) (T : Subgroup X)
    (hT : ¬ 2 ∣ T.index) : T.map π = ⊤ := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have h1 : (T.map π).index ∣ T.index := Subgroup.index_map_dvd T hπ
  obtain ⟨n, hn⟩ := hQ.index (T.map π)
  have hn0 : n = 0 := by
    by_contra hne
    apply hT
    exact dvd_trans (by rw [hn]; exact dvd_pow_self 2 hne) h1
  rw [hn0, pow_zero] at hn
  exact Subgroup.index_eq_one.mp hn

instance instLBarNormal (z : G) : (LBar z).Normal := LBar_normal z

noncomputable def piL (z : G) : ↥(Cen z) →* CentralizerBar z ⧸ LBar z :=
  (QuotientGroup.mk' (LBar z)).comp (toBar z)

theorem piL_eq_one_iff (z : G) {s : G} (hs : s ∈ Cen z) (h2 : ∃ a : ℕ, orderOf s = 2 ^ a) :
    piL z ⟨s, hs⟩ = 1 ↔ s ∈ LC z := by
  constructor
  · intro h
    have h1 : toBar z ⟨s, hs⟩ ∈ LBar z := (QuotientGroup.eq_one_iff _).mp h
    exact mem_LC_of_toBar_mem z hs h2 h1
  · intro h
    have h1 : toBar z ⟨s, hs⟩ ∈ LBar z := ⟨⟨s, hs⟩, h, rfl⟩
    exact (QuotientGroup.eq_one_iff _).mpr h1

theorem Stage1M12.index_facts (hM : Stage1M12 G z S) :
    LBar z ≠ ⊤ ∧ Nat.card (CentralizerBar z ⧸ LBar z) ≤ 2 ∧
      IsPGroup 2 (CentralizerBar z ⧸ LBar z) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨A, -, hLeq, hres, -, -, -⟩ := hM.L_shape
  obtain ⟨hWn, ⟨e⟩⟩ := hM.quot
  have hW6 : (WBar z).index = 6 := by
    show Nat.card (CentralizerBar z ⧸ WBar z) = 6
    rw [Nat.card_congr e.toEquiv, Nat.card_eq_fintype_card, Fintype.card_perm, Fintype.card_fin]
    rfl
  have hWle : WBar z ≤ LBar z := by
    rw [hLeq, hres]
    exact le_sup_left
  have hdvd : (LBar z).index ∣ 6 := hW6 ▸ Subgroup.index_dvd_of_le hWle
  have hPG : IsPGroup 2 (CentralizerBar z ⧸ LBar z) :=
    isPGroup_quotient_of_oResidual_le' (LBar z) (by rw [hLeq])
  obtain ⟨n, hn⟩ := hPG.exists_card_eq
  have hcardL : Nat.card (CentralizerBar z ⧸ LBar z) ∣ 6 := hdvd
  rw [hn] at hcardL
  have hle6 : 2 ^ n ≤ 6 := Nat.le_of_dvd (by norm_num) hcardL
  have hn3 : n < 3 := by
    by_contra hc
    have : 2 ^ 3 ≤ 2 ^ n := Nat.pow_le_pow_right (by norm_num) (not_lt.mp hc)
    omega
  have hn2 : n ≤ 1 := by
    by_contra hc
    have h2 : n = 2 := by omega
    subst h2
    exact absurd hcardL (by decide)
  refine ⟨?_, ?_, hPG⟩
  · intro htop
    obtain ⟨φ, hφ⟩ : ∃ φ : CentralizerBar z →* Equiv.Perm (Fin 3), Function.Surjective φ :=
      ⟨e.toMonoidHom.comp (QuotientGroup.mk' (WBar z)),
        e.surjective.comp (QuotientGroup.mk'_surjective _)⟩
    have h1 := map_oResidual φ hφ (p := 2) Nat.prime_two
    rw [← hLeq, htop, Subgroup.map_top_of_surjective φ hφ] at h1
    exact oResidual_perm3_ne_top h1.symm
  · rw [hn]
    calc 2 ^ n ≤ 2 ^ 1 := Nat.pow_le_pow_right (by norm_num) hn2
      _ = 2 := rfl

theorem Stage2Ctx.sylow_index_odd (h : Stage2Ctx G z k S) : ¬ 2 ∣ (S.subgroupOf (Cen z)).index := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  exact (CFSG.ABGLocalTools.isSylowOf_iff.mp h.sylow).2.2

theorem Stage2Ctx.m12_RC (h : Stage2Ctx G z k S) (hM : Stage1M12 G z S) :
    (RC S z).relIndex S ≤ 2 ∧ RC S z ≠ S := by
  obtain ⟨hne, hcard, hPG⟩ := hM.index_facts
  let ρ : ↥S →* CentralizerBar z ⧸ LBar z := (piL z).comp (Subgroup.inclusion h.S_le_Cen)
  have hker : ρ.ker = (RC S z).subgroupOf S := by
    ext ⟨s, hs⟩
    rw [MonoidHom.mem_ker, Subgroup.mem_subgroupOf]
    show piL z ⟨s, h.S_le_Cen hs⟩ = 1 ↔ s ∈ RC S z
    rw [piL_eq_one_iff z (h.S_le_Cen hs) (orderOf_mem_S h hs)]
    simp [RC, hs]
  refine ⟨?_, ?_⟩
  · calc (RC S z).relIndex S = ((RC S z).subgroupOf S).index := rfl
      _ = ρ.ker.index := by rw [hker]
      _ = Nat.card ρ.range := Subgroup.index_ker ρ
      _ ≤ Nat.card (CentralizerBar z ⧸ LBar z) := Subgroup.card_le_card_group _
      _ ≤ 2 := hcard
  · intro hRS
    apply hne
    have htop : (S.subgroupOf (Cen z)).map (piL z) = ⊤ :=
      map_eq_top_of_isPGroup_of_odd_index (piL z)
        ((QuotientGroup.mk'_surjective _).comp (toBar_surjective z)) hPG _ h.sylow_index_odd
    have hS_le : S ≤ LC z := by
      have : RC S z ≤ LC z := inf_le_right
      rw [hRS] at this
      exact this
    have hbot : (S.subgroupOf (Cen z)).map (piL z) = ⊥ := by
      rw [eq_bot_iff]
      rintro _ ⟨⟨s, hsC⟩, hsT, rfl⟩
      have hs : s ∈ S := hsT
      rw [Subgroup.mem_bot]
      exact (piL_eq_one_iff z hsC (orderOf_mem_S h hs)).mpr (hS_le hs)
    have hsub : ∀ q : CentralizerBar z ⧸ LBar z, q = 1 := fun q => by
      have hq : q ∈ (⊤ : Subgroup (CentralizerBar z ⧸ LBar z)) := trivial
      rw [← htop, hbot] at hq
      exact hq
    have hcard1 : Nat.card (CentralizerBar z ⧸ LBar z) = 1 := by
      rw [Nat.card_eq_one_iff_unique]
      exact ⟨⟨fun a b => (hsub a).trans (hsub b).symm⟩, ⟨1⟩⟩
    exact Subgroup.index_eq_one.mp hcard1

theorem conjugate_eq_self_of_mem_normalizer {X : Type*} [Group X] {H : Subgroup X} {g : X}
    (hg : g ∈ normalizer (H : Set X)) : conjugate H g = H := by
  ext x
  show x ∈ H.map (MulAut.conj g⁻¹).toMonoidHom ↔ x ∈ H
  rw [Subgroup.mem_map_equiv]
  have := (Subgroup.mem_normalizer_iff.mp hg x).symm
  simpa using this

theorem Stage2Ctx.lemma23_ab (h : Stage2Ctx G z k S) :
    ((RC S z).relIndex S ≤ 4 ∧ ((RC S z).relIndex S = 4 → ∃ ε : Bool, k = Kind.l4 ε)) ∧
      (RC S z = S → k = Kind.mcl ∨ k = Kind.ly) := by
  have hd := h.data
  cases hd with
  | g2 hd =>
    obtain ⟨r₁, r₂, L₁, L₂, hsh⟩ := hd.shape
    have hidx : (RC S z).relIndex S = 2 := hsh.2.2.2.2.2.2.2.2.2.1
    refine ⟨⟨by omega, fun h4 => by omega⟩, fun hRS => ?_⟩
    rw [hRS, Subgroup.relIndex_self] at hidx
    omega
  | m12 hM =>
    obtain ⟨hle, hne⟩ := h.m12_RC hM
    exact ⟨⟨by omega, fun h4 => by omega⟩, fun hRS => absurd hRS hne⟩
  | psp4 hP =>
    obtain ⟨q, L₁, L₂, hP⟩ := hP
    refine ⟨⟨by rw [hP.index]; norm_num, fun h4 => by rw [hP.index] at h4; omega⟩, fun hRS => ?_⟩
    have := hP.index
    rw [hRS, Subgroup.relIndex_self] at this
    omega
  | l4 ε hL =>
    obtain ⟨q, L₁, L₂, hL⟩ := hL
    refine ⟨⟨hL.index_le, fun _ => ⟨ε, rfl⟩⟩, fun hRS => ?_⟩
    exfalso
    obtain ⟨s, hsS, hsC, hc1, hc2⟩ := hL.pair.swap
    have hsL : s ∈ LC z := by
      have : RC S z ≤ LC z := inf_le_right
      rw [hRS] at this
      exact this hsS
    have hbar : toBar z ⟨s, hsC⟩ ∈ LBar z := ⟨⟨s, hsC⟩, hsL, rfl⟩
    have hnorm : LBar z ≤ normalizer (L₁ : Set (CentralizerBar z)) := by
      rw [← hL.pair.prod.1]
      refine sup_le Subgroup.le_normalizer ?_
      intro b hb
      apply Subgroup.centralizer_le_normalizer
      rw [Subgroup.mem_centralizer_iff]
      intro a ha
      exact hL.pair.prod.2.1 a ha b hb
    have := conjugate_eq_self_of_mem_normalizer (hnorm hbar)
    rw [hc1] at this
    exact hL.pair.ne this.symm
  | mcl hS =>
    obtain ⟨n, -, hS⟩ := hS
    have hSL : S ≤ LC z := fun s hs =>
      mem_LC_of_toBar_mem z (h.S_le_Cen hs) (orderOf_mem_S h hs) (by rw [hS.eq_L]; trivial)
    have hRS : RC S z = S := inf_eq_left.mpr hSL
    exact ⟨⟨by rw [hRS, Subgroup.relIndex_self]; norm_num, fun h4 => by
      rw [hRS, Subgroup.relIndex_self] at h4; omega⟩, fun _ => Or.inl rfl⟩
  | ly hS =>
    obtain ⟨n, -, hS⟩ := hS
    have hSL : S ≤ LC z := fun s hs =>
      mem_LC_of_toBar_mem z (h.S_le_Cen hs) (orderOf_mem_S h hs) (by rw [hS.eq_L]; trivial)
    have hRS : RC S z = S := inf_eq_left.mpr hSL
    exact ⟨⟨by rw [hRS, Subgroup.relIndex_self]; norm_num, fun h4 => by
      rw [hRS, Subgroup.relIndex_self] at h4; omega⟩, fun _ => Or.inr rfl⟩

theorem Stage2Ctx.lemma23_abc (h : Stage2Ctx G z k S) :
    ((RC S z).relIndex S ≤ 4 ∧ ((RC S z).relIndex S = 4 → ∃ ε : Bool, k = Kind.l4 ε)) ∧
      (RC S z = S → k = Kind.mcl ∨ k = Kind.ly) ∧
      (RC S z ≠ S → ∃ s ∈ S, s ∉ RC S z ∧ orderOf s = 2) :=
  ⟨h.lemma23_ab.1, h.lemma23_ab.2, h.data.base.inv_out⟩

end L23

end CFSG.GH74.GLS.Stage2.Local
