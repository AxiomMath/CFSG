module

public import CFSG.LocalAnalysis.RankThreeUC.AGL81S15R1511B
public import CFSG.LocalAnalysis.RankThreeUC.AGL81S15RowStmts

public section

namespace CFSG.LocalAnalysis.RankThreeUC.S15

open CFSG.AGLEmbeddingD2.McLaughlin.WeakBlockModuleData CFSG.Open
open scoped commutatorElement

section QVersions

variable {X : Type} [Group X] [Finite X]

@[expose] def U4DataAt (p : ℕ) (X : Type) [Group X] [Finite X] : Prop :=
  ∃ d : TauCeti.ValidLieTypeIndex,
    (∃ q : TauCeti.PrimePower, q.p = 2 ∧ d.1 = .twistedA 3 q ∧ p ∣ q.card + 1) ∧
    Nonempty ((↥(pElementSubgroup p (⊤ : Subgroup X)) ⧸
      CFSG.pCore 2 ↥(pElementSubgroup p (⊤ : Subgroup X))) ≃* (TauCeti.CFSGIndex.lie d).Group)

theorem pElementSubgroup_eq_of_isComponent_at {Y : Type} [Group Y] [Finite Y] {Ls : Subgroup Y}
    {q : ℕ} (hq : q.Prime) (hLs : IsComponentOf Ls ⊤)
    (hy : ¬ pElementSubgroup q Ls ≤ (Subgroup.center ↥Ls).map Ls.subtype) :
    pElementSubgroup q Ls = Ls := by
  obtain ⟨-, -, hperf, hsimp⟩ := hLs
  have hOle : pElementSubgroup q Ls ≤ Ls := pElementSubgroup_le Ls
  set O : Subgroup ↥Ls := (pElementSubgroup q Ls).subgroupOf Ls with hO
  have hOn : O.Normal := by
    refine ⟨fun n hn g => ?_⟩
    have hn' : (n : Y) ∈ pElementSubgroup q Ls := hn
    have key : ∀ x ∈ pElementSubgroup q Ls, (g : Y) * x * (g : Y)⁻¹ ∈ pElementSubgroup q Ls := by
      intro x hx
      unfold pElementSubgroup at hx ⊢
      induction hx using Subgroup.closure_induction with
      | mem x hx =>
        apply Subgroup.subset_closure
        refine ⟨Ls.mul_mem (Ls.mul_mem g.2 hx.1) (Ls.inv_mem g.2), ?_⟩
        obtain ⟨k, hk⟩ := hx.2
        refine ⟨k, ?_⟩
        have := orderOf_injective (MulAut.conj (g : Y)).toMonoidHom (MulAut.conj (g : Y)).injective x
        simpa [MulAut.conj_apply, hk] using this
      | one => simpa using Subgroup.one_mem _
      | mul x y _ _ hx hy =>
        have : (g : Y) * (x * y) * (g : Y)⁻¹ = ((g : Y) * x * (g : Y)⁻¹) * ((g : Y) * y * (g : Y)⁻¹) := by group
        rw [this]
        exact Subgroup.mul_mem _ hx hy
      | inv x _ hx =>
        have : (g : Y) * x⁻¹ * (g : Y)⁻¹ = ((g : Y) * x * (g : Y)⁻¹)⁻¹ := by group
        rw [this]
        exact Subgroup.inv_mem _ hx
    show ((g * n * g⁻¹ : ↥Ls) : Y) ∈ pElementSubgroup q Ls
    simpa using key _ hn'
  haveI := hOn
  haveI : (O.map (QuotientGroup.mk' (Subgroup.center ↥Ls))).Normal :=
    hOn.map _ (QuotientGroup.mk'_surjective _)
  have hbt := hsimp.eq_bot_or_eq_top_of_normal (O.map (QuotientGroup.mk' (Subgroup.center ↥Ls)))
  rcases hbt with hbot | htop
  · exfalso
    apply hy
    intro x hx
    have hxO : (⟨x, hOle hx⟩ : ↥Ls) ∈ O := hx
    have h1 : QuotientGroup.mk' (Subgroup.center ↥Ls) ⟨x, hOle hx⟩ ∈
        O.map (QuotientGroup.mk' (Subgroup.center ↥Ls)) := ⟨_, hxO, rfl⟩
    rw [hbot, Subgroup.mem_bot] at h1
    exact ⟨⟨x, hOle hx⟩, (QuotientGroup.eq_one_iff _).1 h1, rfl⟩
  ·
    have hsplit : ∀ a : ↥Ls, ∃ o ∈ O, ∃ z ∈ Subgroup.center ↥Ls, a = o * z := by
      intro a
      have h1 : QuotientGroup.mk' (Subgroup.center ↥Ls) a ∈
          O.map (QuotientGroup.mk' (Subgroup.center ↥Ls)) := by
        rw [htop]
        exact Subgroup.mem_top _
      obtain ⟨o, ho, hoa⟩ := h1
      refine ⟨o, ho, o⁻¹ * a, ?_, by simp⟩
      have : QuotientGroup.mk' (Subgroup.center ↥Ls) (o⁻¹ * a) = 1 := by
        rw [map_mul, map_inv, hoa, inv_mul_cancel]
      exact (QuotientGroup.eq_one_iff _).1 this
    have hcomm : ∀ a b : ↥Ls, ⁅a, b⁆ ∈ O := by
      intro a b
      obtain ⟨o, ho, z, hz, rfl⟩ := hsplit a
      obtain ⟨o', ho', z', hz', rfl⟩ := hsplit b
      have hπ : ∀ x ∈ O, QuotientGroup.mk' O x = 1 := fun x hx => (QuotientGroup.eq_one_iff x).2 hx
      have hzz : ⁅z, z'⁆ = 1 :=
        commutatorElement_eq_one_iff_mul_comm.2 (Subgroup.mem_center_iff.1 hz' z)
      apply (QuotientGroup.eq_one_iff _).1
      change (QuotientGroup.mk' O) ⁅o * z, o' * z'⁆ = 1
      rw [map_commutatorElement, map_mul, map_mul, hπ o ho, hπ o' ho', one_mul, one_mul,
        ← map_commutatorElement, hzz, map_one]
    have hbtop : (⊤ : Subgroup ↥Ls) ≤ O := by
      rw [← hperf, _root_.commutator_def]
      exact (Subgroup.commutator_le).2 (fun a _ b _ => hcomm a b)
    apply le_antisymm hOle
    intro x hx
    exact hbtop (Subgroup.mem_top ⟨x, hx⟩)

theorem normal_of_pElement_le_comap_at {T : Subgroup X} {Ls : Subgroup (X ⧸ gnC T)} {q : ℕ}
    (hq : q.Prime) (hLs : IsComponentOf Ls ⊤)
    (hle : pElementSubgroup q (⊤ : Subgroup X) ≤ Ls.comap (toStar T))
    (hy : ¬ pElementSubgroup q Ls ≤ (Subgroup.center ↥Ls).map Ls.subtype) : Ls.Normal := by
  obtain ⟨y, hyL, hyZ, k, hk⟩ := exists_pElement_not_mem q Ls _ hy
  have hconj : ∀ g : X ⧸ gnC T, Ls.map (MulAut.conj g).toMonoidHom = Ls := by
    intro g
    by_contra hne
    set Ls' := Ls.map (MulAut.conj g).toMonoidHom with hLs'
    have hL' : IsComponentOf Ls' ⊤ := isComponentOf_conj_aux hLs g
    have hcomm : ⁅Ls, Ls'⁆ = ⊥ := kComp_holds.1 _ Ls Ls' hLs hL' (Ne.symm hne)
    have hcom : ∀ a ∈ Ls, ∀ b ∈ Ls', a * b = b * a := by
      intro a ha b hb
      have h1 := Subgroup.commutator_mem_commutator ha hb
      rw [hcomm, Subgroup.mem_bot] at h1
      exact commutatorElement_eq_one_iff_mul_comm.1 h1
    have hy'L' : g * y * g⁻¹ ∈ Ls' := ⟨y, hyL, by simp [MulAut.conj_apply]⟩
    have hord : ∃ m : ℕ, orderOf (g * y * g⁻¹) = q ^ m := by
      refine ⟨k, ?_⟩
      have := orderOf_injective (MulAut.conj g).toMonoidHom (MulAut.conj g).injective y
      simpa [MulAut.conj_apply, hk] using this
    obtain ⟨u, hu, m, hm⟩ := exists_pPow_lift (toStar T) (QuotientGroup.mk'_surjective _)
      hq hord
    have huL : u ∈ Ls.comap (toStar T) := by
      apply hle
      apply Subgroup.subset_closure
      exact ⟨Subgroup.mem_top u, m, hm⟩
    have hy'L : g * y * g⁻¹ ∈ Ls := by
      rw [← hu]
      exact huL
    apply hyZ
    refine ⟨⟨y, hyL⟩, Subgroup.mem_center_iff.2 ?_, rfl⟩
    intro l
    have h1 := hcom _ hy'L (g * (l : X ⧸ gnC T) * g⁻¹) ⟨l, l.2, by simp [MulAut.conj_apply]⟩
    have h2 : g * ((l : X ⧸ gnC T) * y) * g⁻¹ = g * (y * (l : X ⧸ gnC T)) * g⁻¹ := by
      calc g * ((l : X ⧸ gnC T) * y) * g⁻¹
          = (g * (l : X ⧸ gnC T) * g⁻¹) * (g * y * g⁻¹) := by group
        _ = (g * y * g⁻¹) * (g * (l : X ⧸ gnC T) * g⁻¹) := h1.symm
        _ = g * (y * (l : X ⧸ gnC T)) * g⁻¹ := by group
    exact Subtype.ext (mul_left_cancel (mul_right_cancel h2))
  refine ⟨fun n hn g => ?_⟩
  have : (MulAut.conj (g : X ⧸ gnC T)) n ∈ Ls.map (MulAut.conj (g : X ⧸ gnC T)).toMonoidHom :=
    ⟨n, hn, rfl⟩
  rw [hconj] at this
  simpa [MulAut.conj_apply] using this

theorem pRank_le_pRank_of_le_comap_at {T : Subgroup X} {Ls : Subgroup (X ⧸ gnC T)} {q : ℕ}
    (hq : q.Prime) (hC : ¬ q ∣ Nat.card (gnC T))
    (hle : pElementSubgroup q (⊤ : Subgroup X) ≤ Ls.comap (toStar T)) :
    CFSG.Open.pRank q (⊤ : Subgroup X) ≤ CFSG.Open.pRank q Ls := by
  haveI : Fact (Nat.Prime q) := ⟨hq⟩
  obtain ⟨E, -, hE, hEcard⟩ := CFSG.SectionRank.exists_pRank hq.one_lt (⊤ : Subgroup X)
  have hEle : E ≤ Ls.comap (toStar T) := by
    intro x hx
    apply hle
    apply Subgroup.subset_closure
    refine ⟨Subgroup.mem_top x, ?_⟩
    have h3 : orderOf x ∣ q ^ 1 := by simpa using orderOf_dvd_of_pow_eq_one (hE.2 x hx)
    obtain ⟨m, -, hm⟩ := (Nat.dvd_prime_pow hq).1 h3
    exact ⟨m, hm⟩
  have hinj : Function.Injective ((toStar T).comp E.subtype) := by
    rw [injective_iff_map_eq_one]
    intro x hx
    have hxC : (x : X) ∈ gnC T := (QuotientGroup.eq_one_iff (x : X)).1 hx
    have h3 : orderOf (x : X) ∣ q := orderOf_dvd_of_pow_eq_one (hE.2 x x.2)
    have h4 : orderOf (x : X) ∣ Nat.card (gnC T) := by
      rw [← Subgroup.orderOf_mk (x : X) hxC]
      exact orderOf_dvd_natCard _
    rcases (Nat.dvd_prime hq).1 h3 with h | h
    · exact Subtype.ext (orderOf_eq_one_iff.1 h)
    · exact absurd (h ▸ h4) hC
  have := hE.1
  exact CFSG.SectionRank.le_pRank_of_injective hq.one_lt (fun a b => mul_comm' a b)
    (fun a => Subtype.ext (hE.2 a a.2)) hEcard ((toStar T).comp E.subtype) hinj
    (by rintro _ ⟨x, rfl⟩; exact hEle x.2)

theorem three_le_pRank_of_le_comap_at {T : Subgroup X} {Ls : Subgroup (X ⧸ gnC T)} {q : ℕ}
    (hq : q.Prime) (hC : ¬ q ∣ Nat.card (gnC T))
    (hle : pElementSubgroup q (⊤ : Subgroup X) ≤ Ls.comap (toStar T))
    (hX : CFSG.Open.pRank q (⊤ : Subgroup X) = 3) : 3 ≤ CFSG.Open.pRank q Ls := by
  simpa [hX] using pRank_le_pRank_of_le_comap_at hq hC hle

theorem pElement_le_lift_aux1_at {L C : Subgroup X} [L.Normal] [C.Normal] {q : ℕ} (hq : q.Prime)
    (hC : ¬ q ∣ Nat.card C) {x : X} (hx : x ∈ L ⊔ C) {k : ℕ} (hk : orderOf x = q ^ k) : x ∈ L := by
  obtain ⟨l, hl, c, hc, rfl⟩ := Subgroup.mem_sup_of_normal_right.1 hx
  have h1 : orderOf (QuotientGroup.mk' L (l * c)) ∣ q ^ k := hk ▸ orderOf_map_dvd _ _
  have hl1 : QuotientGroup.mk' L l = 1 := (QuotientGroup.eq_one_iff l).2 hl
  have h2 : QuotientGroup.mk' L (l * c) = QuotientGroup.mk' L c := by
    rw [map_mul, hl1, one_mul]
  have h3 : orderOf (QuotientGroup.mk' L (l * c)) ∣ Nat.card C := by
    rw [h2]
    refine (orderOf_map_dvd _ _).trans ?_
    rw [← Subgroup.orderOf_mk c hc]
    exact orderOf_dvd_natCard _
  have hcop : Nat.Coprime (q ^ k) (Nat.card C) :=
    Nat.Coprime.pow_left k ((Nat.Prime.coprime_iff_not_dvd hq).2 hC)
  have h4 : orderOf (QuotientGroup.mk' L (l * c)) = 1 :=
    Nat.dvd_one.1 (hcop.gcd_eq_one ▸ Nat.dvd_gcd h1 h3)
  exact (QuotientGroup.eq_one_iff (l * c)).1 (orderOf_eq_one_iff.1 h4)

theorem pElement_le_lift_at {T L : Subgroup X} {Ls : Subgroup (X ⧸ gnC T)} {q : ℕ} (hq : q.Prime)
    (hX : GNSetting X T) (hLs : IsComponentOf Ls ⊤) (hnorm : Ls.Normal) (hL : LiftOf T L Ls)
    (hC : ¬ q ∣ Nat.card (gnC T))
    (hle : pElementSubgroup q (⊤ : Subgroup X) ≤ Ls.comap (toStar T)) :
    L.Normal ∧ pElementSubgroup q (⊤ : Subgroup X) ≤ L := by
  haveI := hnorm
  have hLn : L.Normal := by
    refine ⟨fun n hn g => ?_⟩
    have hg : toStar T g ∈ Subgroup.normalizer (Ls : Set (X ⧸ gnC T)) := by
      rw [Subgroup.normalizer_eq_top]
      exact Subgroup.mem_top _
    have h1 := liftOf_conj hX hLs hL g hg
    have h2 : g * n * g⁻¹ ∈ L.map (MulAut.conj g).toMonoidHom :=
      ⟨n, hn, by simp [MulAut.conj_apply]⟩
    rwa [h1] at h2
  refine ⟨hLn, ?_⟩
  have hcomap := (liftOf_central_ext hX hLs hL).2
  refine (Subgroup.closure_le L).2 ?_
  rintro x ⟨-, k, hk⟩
  have hx : x ∈ Ls.comap (toStar T) :=
    hle (Subgroup.subset_closure ⟨Subgroup.mem_top x, k, hk⟩)
  rw [hcomap] at hx
  haveI := hLn
  exact pElement_le_lift_aux1_at hq hC hx hk

theorem lift_inf_gnC_le_pCore_of_isUFour (hKSMU4 : KSMU4) {T L : Subgroup X}
    {Ls : Subgroup (X ⧸ gnC T)} (hX : GNSetting X T) (hLs : IsComponentOf Ls ⊤)
    (hL : LiftOf T L Ls) {c : ℕ → Prop} (hU : IsUFour c ↥Ls) : L ⊓ gnC T ≤ CFSG.pCore 2 X := by
  obtain ⟨Q, hQ2, -, d, hd, ⟨e⟩⟩ := hU
  let φ : X ⧸ CFSG.pCore 2 X →* X ⧸ gnC T :=
    QuotientGroup.map (CFSG.pCore 2 X) (gnC T) (MonoidHom.id X)
      (by rw [Subgroup.comap_id]; exact pCore_le_gnC hX)
  have hφ : ∀ A : Subgroup X, (barO2 A).map φ = A.map (toStar T) := by
    intro A
    unfold barO2
    rw [Subgroup.map_map]
    congr 1
  have hφmk : ∀ x : X, φ (QuotientGroup.mk' (CFSG.pCore 2 X) x) = toStar T x := fun x => rfl
  let f : ↥(barO2 L) →* ↥Ls := (φ.comp (barO2 L).subtype).codRestrict Ls (by
    intro k
    have h : φ k ∈ (barO2 L).map φ := ⟨k, k.2, rfl⟩
    rw [hφ, hL.2] at h
    exact h)
  have hf : Function.Surjective f := by
    rintro ⟨s, hs⟩
    rw [← hL.2, ← hφ] at hs
    obtain ⟨k, hk, rfl⟩ := hs
    exact ⟨⟨k, hk⟩, rfl⟩
  have hcentral := (liftOf_central_ext hX hLs hL).1
  have hkerf : f.ker ≤ Subgroup.center ↥(barO2 L) := by
    intro k hk
    obtain ⟨l, hl, hlk⟩ := k.2
    have h1 : φ k = 1 := by
      have h0 : f k = 1 := MonoidHom.mem_ker.1 hk
      exact congrArg Subtype.val h0
    have h2 : l ∈ gnC T := by
      have h3 : toStar T l = 1 := by
        rw [← hφmk l]
        have : QuotientGroup.mk' (CFSG.pCore 2 X) l = (k : X ⧸ CFSG.pCore 2 X) := hlk
        rw [this]
        exact h1
      exact (QuotientGroup.eq_one_iff l).1 h3
    have h4 : (k : X ⧸ CFSG.pCore 2 X) ∈
        ((L ⊓ gnC T).map (QuotientGroup.mk' (CFSG.pCore 2 X))) :=
      ⟨l, ⟨hl, h2⟩, hlk⟩
    obtain ⟨z, hz, hzk⟩ := hcentral h4
    have : z = k := Subtype.ext hzk
    rwa [← this]
  have hker_eq : f.ker = Subgroup.center ↥(barO2 L) :=
    lift_inf_gnC_le_pCore_of_U4_aux1 f hf hkerf (lift_inf_gnC_le_pCore_of_U4_aux2 hQ2 hd e)
  let eK : (↥(barO2 L) ⧸ Subgroup.center ↥(barO2 L)) ≃* (TauCeti.CFSGIndex.lie d).Group :=
    ((QuotientGroup.quotientMulEquivOfEq hker_eq.symm).trans
      (QuotientGroup.quotientKerEquivOfSurjective f hf)).trans e
  have hcard : Nat.card (Subgroup.center ↥(barO2 L)) = 1 :=
    hKSMU4 ↥(barO2 L) hL.1.component.2.2 d ⟨Q, hQ2, hd⟩ ⟨eK⟩ (centre_barO2_odd hL.1)
  have hbot : Subgroup.center ↥(barO2 L) = ⊥ := Subgroup.eq_bot_of_card_eq _ hcard
  intro x hx
  have h1 := hcentral ⟨x, hx, rfl⟩
  rw [hbot, Subgroup.map_bot, Subgroup.mem_bot] at h1
  exact (QuotientGroup.eq_one_iff x).1 h1

theorem pElement_quot_equiv_at {T L : Subgroup X} {Ls : Subgroup (X ⧸ gnC T)} {q : ℕ} (hq : q.Prime)
    (hX : GNSetting X T) (hLs : IsComponentOf Ls ⊤) (hnorm : Ls.Normal) (hL : LiftOf T L Ls)
    (hC : ¬ q ∣ Nat.card (gnC T))
    (hle : pElementSubgroup q (⊤ : Subgroup X) ≤ Ls.comap (toStar T))
    (hy : ¬ pElementSubgroup q Ls ≤ (Subgroup.center ↥Ls).map Ls.subtype)
    (hker : L ⊓ gnC T ≤ CFSG.pCore 2 X) :
    Nonempty ((↥(pElementSubgroup q (⊤ : Subgroup X)) ⧸
      CFSG.pCore 2 ↥(pElementSubgroup q (⊤ : Subgroup X))) ≃* ↥Ls) := by
  have hDn : (pElementSubgroup q (⊤ : Subgroup X)).Normal := pElement_quot_equiv_aux1 q
  obtain ⟨-, hDL⟩ := pElement_le_lift_at hq hX hLs hnorm hL hC hle
  set D := pElementSubgroup q (⊤ : Subgroup X) with hD
  let ψ : ↥D →* ↥Ls := ((toStar T).comp D.subtype).codRestrict Ls (fun d => hle d.2)
  have hLsD : Ls ≤ D.map (toStar T) := by
    have hA11 := pElementSubgroup_eq_of_isComponent_at hq hLs hy
    refine hA11.symm.le.trans ?_
    refine (Subgroup.closure_le _).2 ?_
    rintro y ⟨-, k, hk⟩
    obtain ⟨u, hu, m, hm⟩ := exists_pPow_lift (toStar T) (QuotientGroup.mk'_surjective _)
      hq ⟨k, hk⟩
    exact ⟨u, Subgroup.subset_closure ⟨Subgroup.mem_top u, m, hm⟩, hu⟩
  have hψ : Function.Surjective ψ := by
    rintro ⟨s, hs⟩
    obtain ⟨d, hd, hds⟩ := hLsD hs
    exact ⟨⟨d, hd⟩, Subtype.ext hds⟩
  have hker' : ψ.ker = CFSG.pCore 2 ↥D := by
    refine le_antisymm ?_ ?_
    · intro d hd
      have h1 : toStar T d = 1 := congrArg Subtype.val (MonoidHom.mem_ker.1 hd)
      have h2 : (d : X) ∈ gnC T := (QuotientGroup.eq_one_iff (d : X)).1 h1
      have h3 : (d : X) ∈ CFSG.pCore 2 X := hker ⟨hDL d.2, h2⟩
      haveI : ((CFSG.pCore 2 X).subgroupOf D).Normal :=
        Subgroup.Normal.subgroupOf CFSG.pCore_normal D
      have hN2 : IsPGroup 2 ↥((CFSG.pCore 2 X).subgroupOf D) :=
        (CFSG.pCore_isPGroup (p := 2) (G := X)).comap_subtype
      exact isC2_normalizer_aux0 hN2 (Subgroup.mem_subgroupOf.2 h3)
    · intro d hd
      rw [MonoidHom.mem_ker]
      apply Subtype.ext
      have h1 : (d : X) ∈ CFSG.pCore 2 X := pElement_quot_equiv_aux2 hDn ⟨d, hd, rfl⟩
      have h2 : (d : X) ∈ gnC T := pCore_le_gnC hX h1
      exact (QuotientGroup.eq_one_iff (d : X)).2 h2
  exact ⟨(QuotientGroup.quotientMulEquivOfEq hker'.symm).trans
    (QuotientGroup.quotientKerEquivOfSurjective ψ hψ)⟩

theorem u4DataAt_of_lift (hKSMU4 : KSMU4) {T L : Subgroup X} {Ls : Subgroup (X ⧸ gnC T)} {p : ℕ}
    (hp : p.Prime) (hX : GNSetting X T) (hLs : IsComponentOf Ls ⊤) (hnorm : Ls.Normal)
    (hL : LiftOf T L Ls) (hC : ¬ p ∣ Nat.card (gnC T))
    (hle : pElementSubgroup p (⊤ : Subgroup X) ≤ Ls.comap (toStar T))
    (hy : ¬ pElementSubgroup p Ls ≤ (Subgroup.center ↥Ls).map Ls.subtype)
    (hU : IsUFour (fun Q => p ∣ Q + 1) ↥Ls) : U4DataAt p X := by
  unfold U4DataAt
  have hU' := hU
  obtain ⟨Q, hQ2, hc, d, hd, ⟨e⟩⟩ := hU
  have hker := lift_inf_gnC_le_pCore_of_isUFour hKSMU4 hX hLs hL hU'
  obtain ⟨φ⟩ := pElement_quot_equiv_at hp hX hLs hnorm hL hC hle hy hker
  exact ⟨d, ⟨Q, hQ2, hd, hc⟩, ⟨φ.trans e⟩⟩

theorem u4Shape_of_u4DataAt_aux1 {G : Type} [Group G] (M : Subgroup G) (p : ℕ) :
    (pElementSubgroup p (⊤ : Subgroup ↥M)).map M.subtype =
      CFSG.RankThree.PartOne.pElementSubgroup p M := by
  unfold pElementSubgroup CFSG.RankThree.PartOne.pElementSubgroup
  rw [MonoidHom.map_closure]
  congr 1
  ext y
  constructor
  · rintro ⟨x, ⟨-, k, hk⟩, rfl⟩
    exact ⟨x.2, k, by rw [← hk]; exact Subgroup.orderOf_coe x⟩
  · rintro ⟨hyM, k, hk⟩
    exact ⟨⟨y, hyM⟩, ⟨Subgroup.mem_top _, k, by rw [← hk]; exact Subgroup.orderOf_mk y hyM⟩, rfl⟩

theorem u4Shape_of_u4DataAt {G : Type} [Group G] [Finite G] (M : Subgroup G) (p : ℕ)
    (h : U4DataAt p ↥M) : U4Shape p M := by
  unfold U4DataAt at h
  unfold U4Shape
  obtain ⟨d, hdq, ⟨φ⟩⟩ := h
  refine ⟨d, hdq, ?_⟩
  let DX : Subgroup ↥M := pElementSubgroup p (⊤ : Subgroup ↥M)
  let e : ↥DX ≃* ↥(CFSG.RankThree.PartOne.pElementSubgroup p M) :=
    (DX.equivMapOfInjective M.subtype M.subtype_injective).trans
      (MulEquiv.subgroupCongr (u4Shape_of_u4DataAt_aux1 M p))
  have hc : (CFSG.pCore 2 ↥DX).map e.toMonoidHom =
      CFSG.pCore 2 ↥(CFSG.RankThree.PartOne.pElementSubgroup p M) := CFSG.pCore_map_iso 2 e
  exact ⟨(QuotientGroup.congr (CFSG.pCore 2 ↥DX)
    (CFSG.pCore 2 ↥(CFSG.RankThree.PartOne.pElementSubgroup p M)) e hc).symm.trans φ⟩

end QVersions

end CFSG.LocalAnalysis.RankThreeUC.S15
