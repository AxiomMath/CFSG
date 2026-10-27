module

public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.Setup.FamilyStatements

public section

namespace CFSG.QuasithinUnique.Setup.Family

open Subgroup

theorem map_center_mulEquiv {G : Type*} [Group G] (e : G ≃* G) :
    (Subgroup.center G).map e.toMonoidHom = Subgroup.center G := by
  ext z
  constructor
  · rintro ⟨c, hc, rfl⟩
    have hc' := Subgroup.mem_center_iff.1 hc
    rw [Subgroup.mem_center_iff]
    intro g
    have := hc' (e.symm g)
    simpa using congrArg e this
  · intro hz
    have hz' := Subgroup.mem_center_iff.1 hz
    refine ⟨e.symm z, ?_, by simp⟩
    show e.symm z ∈ Subgroup.center G
    rw [Subgroup.mem_center_iff]
    intro g
    apply e.injective
    simpa using hz' (e g)

theorem center_eq_bot_of_simple_nonabelian {S : Type*} [Group S] [IsSimpleGroup S]
    (hnonab : ∃ a b : S, a * b ≠ b * a) : Subgroup.center S = ⊥ := by
  rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal (Subgroup.center S) with h | h
  · exact h
  · exfalso
    obtain ⟨a, b, hab⟩ := hnonab
    have : a ∈ Subgroup.center S := by rw [h]; trivial
    exact hab ((Subgroup.mem_center_iff.1 this b).symm)

theorem conj_injective_of_center_eq_bot {S : Type*} [Group S] (hZ : Subgroup.center S = ⊥) :
    Function.Injective (MulAut.conj : S →* MulAut S) := by
  intro a b hab
  have : a⁻¹ * b ∈ Subgroup.center S := by
    rw [Subgroup.mem_center_iff]
    intro g
    have h1 : a * g * a⁻¹ = b * g * b⁻¹ := by
      have := congrArg (fun φ : MulAut S => φ g) hab
      simpa [MulAut.conj_apply] using this
    calc g * (a⁻¹ * b) = a⁻¹ * (a * g * a⁻¹) * b := by group
      _ = a⁻¹ * (b * g * b⁻¹) * b := by rw [h1]
      _ = a⁻¹ * b * g := by group
  rw [hZ, Subgroup.mem_bot] at this
  exact (inv_mul_eq_one.1 this)

theorem normal_two_subgroup_aut_eq_bot {S : Type*} [Group S] [Finite S] [IsSimpleGroup S]
    (hnonab : ∃ a b : S, a * b ≠ b * a)
    (D : Subgroup (MulAut S)) (hD : (MulAut.conj : S →* MulAut S).range ≤ D)
    (N : Subgroup (MulAut S)) (hND : N ≤ D) (hNn : (N.subgroupOf D).Normal)
    (hN2 : IsPGroup 2 N) : N = ⊥ := by
  have hZ := center_eq_bot_of_simple_nonabelian hnonab
  have hinj := conj_injective_of_center_eq_bot hZ
  let Inn : Subgroup (MulAut S) := (MulAut.conj : S →* MulAut S).range
  have hNnorm : ∀ n ∈ N, ∀ d ∈ D, d * n * d⁻¹ ∈ N := fun n hn d hd =>
    (Subgroup.normal_subgroupOf_iff hND).1 hNn n d hn hd
  have hconjAut : ∀ (φ : MulAut S) (s : S), (MulAut.conj (φ s) : MulAut S) =
      φ * MulAut.conj s * φ⁻¹ := by
    intro φ s
    ext x
    simp [MulAut.conj_apply]
  have hInnNorm : ∀ i ∈ Inn, ∀ φ : MulAut S, φ * i * φ⁻¹ ∈ Inn := by
    rintro _ ⟨s, rfl⟩ φ
    exact ⟨φ s, (hconjAut φ s)⟩
  have hK : N ⊓ Inn = ⊥ := by
    let K' : Subgroup S := (N ⊓ Inn).comap (MulAut.conj : S →* MulAut S)
    have hK'n : K'.Normal := ⟨fun x hx s => by
      refine ⟨?_, ⟨s * x * s⁻¹, rfl⟩⟩
      have hs : (MulAut.conj s : MulAut S) ∈ D := hD ⟨s, rfl⟩
      have := hNnorm _ hx.1 _ hs
      simpa using this⟩
    rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal K' with h | h
    · rw [eq_bot_iff]
      rintro φ ⟨hφN, x, rfl⟩
      have : x ∈ K' := ⟨hφN, ⟨x, rfl⟩⟩
      rw [h, Subgroup.mem_bot] at this
      rw [this, map_one]
      exact Subgroup.one_mem _
    · exfalso
      have hInnN : ∀ x : S, (MulAut.conj x : MulAut S) ∈ N := fun x => by
        have : x ∈ K' := by rw [h]; trivial
        exact this.1
      let ψ : S →* N := (MulAut.conj : S →* MulAut S).codRestrict N hInnN
      have hψ : Function.Injective ψ := fun a b hab => hinj (congrArg Subtype.val hab)
      have hS2 : IsPGroup 2 S := hN2.of_injective ψ hψ
      have := hS2.center_nontrivial
      rw [hZ] at this
      exact not_nontrivial _ this
  rw [eq_bot_iff]
  intro n hn
  have hcomm : ∀ s : S, n * MulAut.conj s * n⁻¹ = MulAut.conj s := by
    intro s
    have hs : (MulAut.conj s : MulAut S) ∈ D := hD ⟨s, rfl⟩
    have h1 : n * MulAut.conj s * n⁻¹ * (MulAut.conj s)⁻¹ ∈ N ⊓ Inn := by
      constructor
      · have h2 := hNnorm n⁻¹ (inv_mem hn) _ hs
        have h3 : n * MulAut.conj s * n⁻¹ * (MulAut.conj s)⁻¹ =
            n * (MulAut.conj s * n⁻¹ * (MulAut.conj s)⁻¹) := by group
        rw [h3]
        exact mul_mem hn h2
      · have hi : (MulAut.conj s : MulAut S) ∈ Inn := ⟨s, rfl⟩
        exact Subgroup.mul_mem _ (hInnNorm _ hi n) (Subgroup.inv_mem _ hi)
    rw [hK, Subgroup.mem_bot, mul_inv_eq_one] at h1
    exact h1
  have hfix : ∀ s : S, n s = s := by
    intro s
    apply hinj
    rw [hconjAut, hcomm]
  rw [Subgroup.mem_bot]
  ext s
  simpa using hfix s

section Construct

variable {G : Type} [Group G] {H L : Subgroup G}

theorem conj_mem_of_normal (hLH : L ≤ H) (hLn : (L.subgroupOf H).Normal) (h : G) (hh : h ∈ H)
    (l : G) (hl : l ∈ L) : h * l * h⁻¹ ∈ L :=
  (Subgroup.normal_subgroupOf_iff hLH).1 hLn l h hl hh

@[expose] def conjAutL (hLH : L ≤ H) (hLn : (L.subgroupOf H).Normal) (h : ↥H) : MulAut ↥L where
  toFun l := ⟨(h : G) * l * (h : G)⁻¹, conj_mem_of_normal hLH hLn h h.2 l l.2⟩
  invFun l := ⟨(h : G)⁻¹ * l * (h : G), by
    simpa using conj_mem_of_normal hLH hLn (h : G)⁻¹ (inv_mem h.2) l l.2⟩
  left_inv l := by ext; simp [mul_assoc]
  right_inv l := by ext; simp [mul_assoc]
  map_mul' a b := by ext; simp [mul_assoc]

theorem conjAutL_apply (hLH : L ≤ H) (hLn : (L.subgroupOf H).Normal) (h : ↥H) (l : ↥L) :
    ((conjAutL hLH hLn h l : ↥L) : G) = (h : G) * l * (h : G)⁻¹ := rfl

@[expose] noncomputable def actionOnCQ (hLH : L ≤ H) (hLn : (L.subgroupOf H).Normal) :
    ↥H →* MulAut (CQ L) where
  toFun h := QuotientGroup.congr (Subgroup.center ↥L) (Subgroup.center ↥L) (conjAutL hLH hLn h)
    (map_center_mulEquiv _)
  map_one' := by
    ext x
    induction x using QuotientGroup.induction_on with
    | H l =>
      show (QuotientGroup.mk (conjAutL hLH hLn 1 l) : CQ L) = QuotientGroup.mk l
      congr 1
      exact Subtype.ext (by simp [conjAutL_apply])
  map_mul' a b := by
    ext x
    induction x using QuotientGroup.induction_on with
    | H l =>
      show (QuotientGroup.mk (conjAutL hLH hLn (a * b) l) : CQ L) =
        QuotientGroup.mk (conjAutL hLH hLn a (conjAutL hLH hLn b l))
      congr 1
      exact Subtype.ext (by simp [conjAutL_apply, mul_assoc])

theorem actionOnCQ_mk (hLH : L ≤ H) (hLn : (L.subgroupOf H).Normal) (h : ↥H) (l : ↥L) :
    actionOnCQ hLH hLn h (QuotientGroup.mk l) =
      QuotientGroup.mk (conjAutL hLH hLn h l) := rfl

theorem isConjAction_actionOnCQ (hLH : L ≤ H) (hLn : (L.subgroupOf H).Normal) :
    IsConjAction H L (actionOnCQ hLH hLn) := by
  intro h l l' hl
  rw [actionOnCQ_mk]
  congr 1
  exact Subtype.ext hl.symm

theorem actionOnCQ_eq_one_iff (hLH : L ≤ H) (hLn : (L.subgroupOf H).Normal)
    (hperf : Group.IsPerfect ↥L) (h : ↥H) :
    actionOnCQ hLH hLn h = 1 ↔ (h : G) ∈ Subgroup.centralizer (L : Set G) := by
  constructor
  · intro hker
    have hz : ∀ l : ↥L, (conjAutL hLH hLn h l)⁻¹ * l ∈ Subgroup.center ↥L := by
      intro l
      have := DFunLike.congr_fun hker (QuotientGroup.mk l)
      rw [actionOnCQ_mk, MulAut.one_apply, QuotientGroup.eq] at this
      exact this
    let φ : ↥L →* ↥(Subgroup.center ↥L) :=
      { toFun := fun l => ⟨(conjAutL hLH hLn h l)⁻¹ * l, hz l⟩
        map_one' := by
          apply Subtype.ext
          simp
        map_mul' := fun a b => by
          apply Subtype.ext
          have h1 := Subgroup.mem_center_iff.1 (hz a) ((conjAutL hLH hLn h b)⁻¹)
          simp only [map_mul, mul_inv_rev, Subgroup.coe_mul]
          calc (conjAutL hLH hLn h b)⁻¹ * (conjAutL hLH hLn h a)⁻¹ * (a * b)
              = (conjAutL hLH hLn h b)⁻¹ * ((conjAutL hLH hLn h a)⁻¹ * a) * b := by group
            _ = ((conjAutL hLH hLn h a)⁻¹ * a) * (conjAutL hLH hLn h b)⁻¹ * b := by rw [h1]
            _ = _ := by group }
    have hcc : ∀ a b : ↥(Subgroup.center ↥L), a * b = b * a := fun a b =>
      Subtype.ext (Subgroup.mem_center_iff.1 b.2 a.1)
    have hker' : commutator ↥L ≤ φ.ker := by
      rw [commutator_def, Subgroup.commutator_le]
      intro a _ b _
      rw [MonoidHom.mem_ker, map_commutatorElement]
      exact commutatorElement_eq_one_iff_mul_comm.2 (hcc _ _)
    rw [Subgroup.mem_centralizer_iff]
    intro x hx
    have hl : (⟨x, hx⟩ : ↥L) ∈ φ.ker := hker' (by rw [hperf.commutator_eq_top]; trivial)
    have h2 : (conjAutL hLH hLn h ⟨x, hx⟩)⁻¹ * ⟨x, hx⟩ = 1 := congrArg Subtype.val hl
    have h3 : conjAutL hLH hLn h ⟨x, hx⟩ = ⟨x, hx⟩ := inv_mul_eq_one.1 h2
    have h4 := congrArg Subtype.val h3
    rw [conjAutL_apply] at h4
    calc x * (h : G) = (h : G) * x * (h : G)⁻¹ * h := by rw [h4]
      _ = h * x := by group
  · intro hc
    ext x
    induction x using QuotientGroup.induction_on with
    | H l =>
      rw [actionOnCQ_mk, MulAut.one_apply]
      congr 1
      apply Subtype.ext
      rw [conjAutL_apply]
      have := Subgroup.mem_centralizer_iff.1 hc l l.2
      calc (h : G) * l * (h : G)⁻¹ = (l : G) * h * (h : G)⁻¹ := by rw [← this]
        _ = l := by group

theorem inn_le_range_actionOnCQ (hLH : L ≤ H) (hLn : (L.subgroupOf H).Normal) :
    (MulAut.conj : CQ L →* MulAut (CQ L)).range ≤ (actionOnCQ hLH hLn).range := by
  rintro _ ⟨s, rfl⟩
  obtain ⟨l, rfl⟩ := QuotientGroup.mk_surjective s
  refine ⟨⟨l, hLH l.2⟩, ?_⟩
  ext x
  induction x using QuotientGroup.induction_on with
  | H y =>
    rw [actionOnCQ_mk, MulAut.conj_apply]
    show _ = (QuotientGroup.mk l * QuotientGroup.mk y * (QuotientGroup.mk l)⁻¹ : CQ L)
    rw [← QuotientGroup.mk_inv, ← QuotientGroup.mk_mul, ← QuotientGroup.mk_mul]
    congr 1

end Construct

theorem isSylowTwoOf_map_range {G : Type} [Group G] {H T : Subgroup G} {D : Type} [Group D]
    (α : ↥H →* D) (hT : IsSylowTwoOf T H) :
    IsSylowTwoOf ((T.subgroupOf H).map α) α.range := by
  refine ⟨Subgroup.map_le_range _ _, ?_, ?_⟩
  · have h2 : IsPGroup 2 (T.subgroupOf H) := by
      have : IsPGroup 2 ↥T := hT.2.1
      exact this.of_equiv (Subgroup.subgroupOfEquivOfLe hT.1).symm
    exact h2.of_surjective (α.subgroupMap _) (α.subgroupMap_surjective _)
  · have heq : ((T.subgroupOf H).map α).subgroupOf α.range =
        (T.subgroupOf H).map α.rangeRestrict := by
      ext y
      simp only [Subgroup.mem_subgroupOf, Subgroup.mem_map]
      constructor
      · rintro ⟨t, ht, hty⟩
        exact ⟨t, ht, Subtype.ext hty⟩
      · rintro ⟨t, ht, hty⟩
        exact ⟨t, ht, congrArg Subtype.val hty⟩
    rw [heq]
    intro hdvd
    exact hT.2.2 (hdvd.trans (Subgroup.index_map_dvd _ α.rangeRestrict_surjective))

theorem maximal_overgroup_map {G D : Type} [Group G] [Group D] {H T M : Subgroup G}
    (α : ↥H →* D) (hTH : T ≤ H) (hker : α.ker ≤ M.subgroupOf H)
    (hM : T ≤ M ∧ M < H ∧ ∀ X : Subgroup G, T ≤ X → X < H → X ≤ M) :
    (T.subgroupOf H).map α ≤ (M.subgroupOf H).map α ∧ (M.subgroupOf H).map α < α.range ∧
    ∀ X : Subgroup D, (T.subgroupOf H).map α ≤ X → X < α.range →
      X ≤ (M.subgroupOf H).map α := by
  refine ⟨Subgroup.map_mono (fun t ht => hM.1 ht), ?_, ?_⟩
  · refine lt_of_le_of_ne (Subgroup.map_le_range _ _) fun h => ?_
    have htop : M.subgroupOf H = ⊤ := by
      rw [eq_top_iff]
      intro x _
      have hx : α x ∈ (M.subgroupOf H).map α := by rw [h]; exact ⟨x, rfl⟩
      obtain ⟨m, hm, hmx⟩ := hx
      have : m⁻¹ * x ∈ α.ker := by
        rw [MonoidHom.mem_ker, map_mul, map_inv, hmx, inv_mul_cancel]
      have h2 : x = m * (m⁻¹ * x) := by group
      rw [h2]
      exact mul_mem hm (hker this)
    have : H ≤ M := by
      intro x hx
      have : (⟨x, hx⟩ : ↥H) ∈ M.subgroupOf H := by rw [htop]; trivial
      exact this
    exact absurd hM.2.1 (not_lt_of_ge this)
  · intro X hTX hXD
    let Y : Subgroup ↥H := X.comap α
    have hTY : T.subgroupOf H ≤ Y := fun t ht => hTX ⟨t, ht, rfl⟩
    have hYtop : Y ≠ ⊤ := by
      intro hY
      apply hXD.ne
      apply le_antisymm hXD.le
      rintro _ ⟨x, rfl⟩
      have : x ∈ Y := by rw [hY]; trivial
      exact this
    have hY0 : Y.map H.subtype < H := by
      refine lt_of_le_of_ne (by rintro _ ⟨y, _, rfl⟩; exact y.2) fun h => hYtop ?_
      rw [eq_top_iff]
      intro y _
      have : (y : G) ∈ Y.map H.subtype := by rw [h]; exact y.2
      obtain ⟨y', hy', hyy'⟩ := this
      have : y' = y := Subtype.ext hyy'
      rwa [this] at hy'
    have hTY0 : T ≤ Y.map H.subtype := fun t ht => ⟨⟨t, hTH ht⟩, hTY ht, rfl⟩
    have hle := hM.2.2 _ hTY0 hY0
    intro x hx
    obtain ⟨y, rfl⟩ := hXD.le.trans' (le_refl X) hx
    refine ⟨y, ?_, rfl⟩
    exact hle ⟨y, hx, rfl⟩

theorem exists_residual_action {G : Type} [Group G] [Finite G] {H T M L : Subgroup G}
    (hLH : L ≤ H) (hLn : (L.subgroupOf H).Normal) (hLq : CFSG.IsQuasisimple ↥L)
    (hC : H ⊓ Subgroup.centralizer (L : Set G) = centerIn L)
    (hZ : Nat.card (centerIn L) = 1 ∨ Nat.card (centerIn L) = 3)
    (hT : IsSylowTwoOf T H) (hTn : ¬ (T.subgroupOf H).Normal)
    (hM : T ≤ M ∧ M < H ∧ ∀ X : Subgroup G, T ≤ X → X < H → X ≤ M) (hcore : centerIn L ≤ M) :
    ∃ α : ↥H →* MulAut (CQ L), IsConjAction H L α ∧ α.ker = (centerIn L).subgroupOf H ∧
      (MulAut.conj : CQ L →* MulAut (CQ L)).range ≤ α.range ∧
      (∀ N : Subgroup (MulAut (CQ L)), N ≤ α.range → (N.subgroupOf α.range).Normal →
        IsPGroup 2 N → N = ⊥) ∧
      Function.Injective (α.comp (T.subgroupOf H).subtype) ∧
      IsSylowTwoOf ((T.subgroupOf H).map α) α.range ∧
      ¬ (((T.subgroupOf H).map α).subgroupOf α.range).Normal ∧
      (T.subgroupOf H).map α ≤ (M.subgroupOf H).map α ∧ (M.subgroupOf H).map α < α.range ∧
      ∀ X : Subgroup (MulAut (CQ L)), (T.subgroupOf H).map α ≤ X → X < α.range →
        X ≤ (M.subgroupOf H).map α := by
  set α := actionOnCQ hLH hLn with hα
  have : IsSimpleGroup (CQ L) := hLq.2.1
  have hker : α.ker = (centerIn L).subgroupOf H := by
    ext h
    rw [MonoidHom.mem_ker, hα, actionOnCQ_eq_one_iff hLH hLn hLq.1 h, Subgroup.mem_subgroupOf,
      ← hC]
    exact ⟨fun hc => ⟨h.2, hc⟩, fun hc => hc.2⟩
  have hO2 : ∀ N : Subgroup (MulAut (CQ L)), N ≤ α.range → (N.subgroupOf α.range).Normal →
      IsPGroup 2 N → N = ⊥ := fun N hND hNn hN2 =>
    normal_two_subgroup_aut_eq_bot hLq.2.2 α.range (inn_le_range_actionOnCQ hLH hLn) N hND hNn hN2
  have hinj : Function.Injective (α.comp (T.subgroupOf H).subtype) := by
    rw [injective_iff_map_eq_one]
    intro t ht
    have h1 : (t : ↥H) ∈ α.ker := ht
    rw [hker, Subgroup.mem_subgroupOf] at h1
    have hzT : (((t : ↥H)) : G) ∈ T := t.2
    have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
    obtain ⟨k, hk⟩ := (IsPGroup.iff_orderOf.1 hT.2.1) ⟨_, hzT⟩
    have hdvd : orderOf (((t : ↥H)) : G) ∣ Nat.card (centerIn L) :=
      Subgroup.orderOf_dvd_natCard _ h1
    have hk' : orderOf (((t : ↥H)) : G) = 2 ^ k := by
      rw [← hk]; exact (Subgroup.orderOf_mk _ _).symm
    rw [hk'] at hdvd
    have hk0 : k = 0 := by
      rcases hZ with h | h <;> rw [h] at hdvd
      · exact (Nat.pow_eq_one.1 (Nat.dvd_one.1 hdvd)).resolve_left (by norm_num)
      · have : 2 ^ k ∣ 3 := hdvd
        by_contra hne
        have h2 : 2 ∣ 3 := (dvd_pow_self 2 hne).trans this
        omega
    rw [hk0, pow_zero, orderOf_eq_one_iff] at hk'
    exact Subtype.ext (Subtype.ext hk')
  have hmax := maximal_overgroup_map α hT.1 (by rw [hker]; exact fun h hh => hcore hh) hM
  refine ⟨α, isConjAction_actionOnCQ hLH hLn, hker, inn_le_range_actionOnCQ hLH hLn, hO2, hinj,
    isSylowTwoOf_map_range α hT, ?_, hmax.1, hmax.2.1, hmax.2.2⟩
  intro hnorm
  have hSyl := isSylowTwoOf_map_range α hT
  have hbot := hO2 _ hSyl.1 hnorm hSyl.2.1
  apply hTn
  have : T.subgroupOf H = ⊥ := by
    rw [eq_bot_iff]
    intro t ht
    have : α t ∈ (T.subgroupOf H).map α := ⟨t, ht, rfl⟩
    rw [hbot, Subgroup.mem_bot] at this
    have := hinj (a₁ := ⟨t, ht⟩) (a₂ := 1) (by simpa using this)
    exact congrArg Subtype.val this
  rw [this]
  infer_instance

end CFSG.QuasithinUnique.Setup.Family
