module

public import CFSG.Holt.H78.Sec4Prop49S4d
public import CFSG.Holt.H78.Lemma27Blocks
import CFSG.Holt.H78.SEModelFive
import CFSG.Holt.H78.Sec4Known
import CFSG.Holt.H78.Sec4LineTheorem
import CFSG.Holt.PermFacts
public import CFSG.Holt.H78.Sec4Prop49S4b
public import CFSG.Holt.H78.Sec4Prop49S4c

public section

namespace CFSG.Holt.H78

open MulAction CFSG.Holt CFSG.Holt.General CFSG.Open Equiv
open scoped Pointwise

section FibreLemma

theorem apply_eq_of_mem_odd_normal {X Δ I : Type*} [Group X] [Fintype I] [DecidableEq I]
    (r : X →* Perm Δ) (φ : X →* Perm I) (f : Δ → I) (hf : Function.Surjective f)
    (heq : ∀ x δ, f (r x δ) = φ x (f δ)) (h5 : 5 ≤ Fintype.card I)
    (hA : alternatingGroup I ≤ φ.range) {Q : Subgroup (Perm Δ)} [Finite Q]
    (hQr : Q ≤ r.range) (hQn : ∀ x : X, ∀ q ∈ Q, r x * q * (r x)⁻¹ ∈ Q)
    (hQodd : Odd (Nat.card Q)) {q : Perm Δ} (hq : q ∈ Q) (δ : Δ) : f (q δ) = f δ := by
  classical
  have hdet : ∀ x : X, r x = 1 → φ x = 1 := fun x hx => Equiv.ext fun p => by
    obtain ⟨δ, rfl⟩ := hf p
    rw [← heq, hx, Perm.one_apply, Perm.one_apply]
  set P := (Q.comap r).map φ with hP
  have hPodd : ∀ p ∈ P, Odd (orderOf p) := by
    rintro _ ⟨n, hn, rfl⟩
    have ho : Odd (orderOf (r n)) := Odd.of_dvd_nat hQodd (Subgroup.orderOf_dvd_natCard Q hn)
    have h1 : φ n ^ orderOf (r n) = 1 := by
      rw [← map_pow, hdet _ (by rw [map_pow, pow_orderOf_eq_one])]
    exact Odd.of_dvd_nat ho (orderOf_dvd_of_pow_eq_one h1)
  have hPA : P ≤ alternatingGroup I := fun p hp => by
    rw [Perm.mem_alternatingGroup]
    obtain ⟨k, hk⟩ := hPodd p hp
    have h := congrArg Perm.sign (pow_orderOf_eq_one p)
    rw [map_pow, map_one, hk, pow_succ, pow_mul, Int.units_sq, one_pow, one_mul] at h
    exact h
  have hPn : (P.subgroupOf (alternatingGroup I)).Normal := ⟨fun p hpP g => by
    obtain ⟨x, hx⟩ := hA g.2
    obtain ⟨n, hn, hnp⟩ := (Subgroup.mem_subgroupOf.mp hpP : (p : Perm I) ∈ P)
    rw [Subgroup.mem_subgroupOf]
    refine ⟨x * n * x⁻¹, ?_, ?_⟩
    · show r (x * n * x⁻¹) ∈ Q
      rw [map_mul, map_mul, map_inv]
      exact hQn x _ hn
    · rw [map_mul, map_mul, map_inv, hx, hnp]
      rfl⟩
  have : IsSimpleGroup (alternatingGroup I) :=
    alternatingGroup.isSimpleGroup (by rwa [Nat.card_eq_fintype_card])
  rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal (P.subgroupOf (alternatingGroup I)) with
    hb | ht
  · obtain ⟨n, hn⟩ := hQr hq
    have hmem : φ n ∈ P := ⟨n, show r n ∈ Q by rw [hn]; exact hq, rfl⟩
    have hmem' : (⟨φ n, hPA hmem⟩ : alternatingGroup I) ∈ P.subgroupOf (alternatingGroup I) :=
      hmem
    rw [hb] at hmem'
    have hφ : φ n = 1 := congrArg Subtype.val (Subgroup.mem_bot.mp hmem')
    rw [← hn, heq, hφ, Perm.one_apply]
  · exfalso
    obtain ⟨e⟩ : Nonempty (Fin 4 ↪ I) := Function.Embedding.nonempty_of_card_le
      (by rw [Fintype.card_fin]; omega)
    have hne : ∀ {i j : Fin 4}, i ≠ j → e i ≠ e j := fun h h' => h (e.injective h')
    set σ := swap (e 0) (e 1) * swap (e 2) (e 3) with hσ
    have hσA : σ ∈ alternatingGroup I := by
      rw [Perm.mem_alternatingGroup, hσ, map_mul, Perm.sign_swap (hne (by decide)),
        Perm.sign_swap (hne (by decide))]
      rfl
    have hmem : (⟨σ, hσA⟩ : alternatingGroup I) ∈ P.subgroupOf (alternatingGroup I) :=
      ht ▸ Subgroup.mem_top _
    have hσσ : σ * σ = 1 := swap_mul_swap_mul_self (hne (by decide)) (hne (by decide))
      (hne (by decide)) (hne (by decide)) (hne (by decide)) (hne (by decide))
    have hσ1 : σ ≠ 1 := fun h => hne (show (0 : Fin 4) ≠ 1 by decide) (by
      have h0 := congrArg (fun π : Perm I => π (e 0)) h
      simp only [hσ, Perm.mul_apply, Perm.one_apply] at h0
      rw [swap_apply_of_ne_of_ne (hne (by decide)) (hne (by decide)), swap_apply_left] at h0
      exact h0.symm)
    have h2 : orderOf σ = 2 := orderOf_eq_prime (by rw [sq]; exact hσσ) hσ1
    have := hPodd σ hmem
    rw [h2] at this
    exact absurd this (by decide)

end FibreLemma

section AFLk

variable {G : Type*} [Group G] [Finite G] {Ω : Type*} [MulAction G Ω]

theorem HoltData.exists_mulEquiv_pairProducts (D : HoltData G Ω) (α β : Ω)
    {L : Subgroup (Subgroup.closure (longInvSwap G Ω α β))} (hL : L.Normal)
    {N : Type*} [Group N] [IsSimpleGroup N] (hN : ∃ a b : N, a * b ≠ b * a)
    {ψ : L →* N} (hψ : Function.Surjective ψ) :
    ∃ k : D.ι, D.M k = alternatingGroup (D.Ψc k) ∧ 7 ≤ Fintype.card (D.Ψc k) ∧
      Nonempty (N ≃* pairProducts (D.ρ k).range (D.coord α k) (D.coord β k)) := by
  classical
  obtain ⟨s, hs⟩ : (longInvSwap G Ω α β).Nonempty := by
    by_contra hne
    rw [Set.not_nonempty_iff_eq_empty] at hne
    have h1 : ∀ x : L, x = 1 := fun x => by
      have hx : ((x : Subgroup.closure (longInvSwap G Ω α β)) : G) ∈ (⊥ : Subgroup G) := by
        rw [← Subgroup.closure_empty, ← hne]
        exact (x : Subgroup.closure (longInvSwap G Ω α β)).2
      exact Subtype.ext (Subtype.ext (Subgroup.mem_bot.mp hx))
    refine not_subsingleton_of_ne_comm hN ⟨fun a b => ?_⟩
    obtain ⟨x, rfl⟩ := hψ a
    obtain ⟨y, rfl⟩ := hψ b
    rw [h1 x, h1 y]
  have hCH : Subgroup.closure (longInvSwap G Ω α β) ≤ jHull G Ω :=
    Subgroup.closure_mono fun t ht => ht.1
  set e : Subgroup.closure (longInvSwap G Ω α β) →* jHull G Ω := Subgroup.inclusion hCH
  set f : Subgroup.closure (longInvSwap G Ω α β) →* (∀ i, Perm (D.Ψc i)) :=
    (MonoidHom.pi D.ρ).comp e
  have hf : Group.IsSolvable f.ker := by
    have := D.isSolvable_jOrbitKernel
    let k : f.ker →* jOrbitKernel G Ω :=
      ((Subgroup.closure (longInvSwap G Ω α β)).subtype.comp f.ker.subtype).codRestrict _
        fun x => (D.mem_jOrbitKernel_iff_rho (h := e x)).mpr fun i => congrFun (x.2 : f x = 1) i
    refine Group.isSolvable_of_isSolvable_injective (f := k) fun x y hxy => ?_
    have := congrArg Subtype.val hxy
    exact Subtype.ext (Subtype.ext this)
  obtain ⟨ψ₁, hψ₁⟩ := exists_surjective_map_of_isSolvable_ker hf hψ hN
  set Q := (Subgroup.closure ((↑) ⁻¹' longInvSwap G Ω α β : Set (jHull G Ω))).map
    (MonoidHom.pi D.ρ)
  have he : e.range = (Subgroup.closure (longInvSwap G Ω α β)).subgroupOf (jHull G Ω) := by
    ext x
    rw [MonoidHom.mem_range, Subgroup.mem_subgroupOf]
    refine ⟨fun ⟨c, hc⟩ => ?_, fun hx => ⟨⟨x, hx⟩, rfl⟩⟩
    rw [← hc]
    exact c.2
  have hrange : f.range = Q := by
    rw [MonoidHom.range_comp, he,
      ← closure_preimage_eq_subgroupOf fun t ht => mem_jHull_of_mem_longInv ht.1]
  set P := Subgroup.pi Set.univ fun i => pairProducts (D.ρ i).range (D.coord α i) (D.coord β i)
  have hLQ : L.map f ≤ Q := hrange ▸ Subgroup.map_le_range f L
  have hLn : ∀ q ∈ Q, ∀ x ∈ L.map f, q * x * q⁻¹ ∈ L.map f := by
    rintro q hq _ ⟨l, hl, rfl⟩
    obtain ⟨c, rfl⟩ : q ∈ f.range := hrange ▸ hq
    exact ⟨c * l * c⁻¹, hL.conj_mem l hl c, by rw [map_mul, map_mul, map_inv]⟩
  have hs' : ((⟨s, mem_jHull_of_mem_longInv hs.1⟩ : jHull G Ω) : G) ∈ longInvSwap G Ω α β := hs
  obtain ⟨ψ₂, hψ₂⟩ := exists_surjective_inf_of_relIndex_le_two hLQ
    (D.relIndex_pi_pairProducts_le_two hs') hψ₁ hN
  have hPQ : P ≤ Q := D.pi_pairProducts_le_map_closure ⟨s, hs⟩
  obtain ⟨i, M, hMP, hMn, ψ₃, hψ₃⟩ := exists_surjective_of_le_pi (L := L.map f ⊓ P)
    inf_le_right (fun p hp x hx => ⟨hLn p (hPQ hp) x hx.1,
      P.mul_mem (P.mul_mem hp hx.2) (P.inv_mem hp)⟩) hψ₂ hN
  have hPns : ¬ Group.IsSolvable (pairProducts (D.ρ i).range (D.coord α i) (D.coord β i)) :=
    fun hsol => by
      have : Group.IsSolvable M :=
        Group.isSolvable_of_isSolvable_injective (Subgroup.inclusion_injective hMP)
      exact not_isSolvable_of_surjective_of_ne_comm hψ₃ hN this
  rcases D.factor i with ⟨hA, h7⟩ | hSE
  · refine ⟨i, hA, h7, ?_⟩
    rcases D.isSolvable_or_alternating_pairProducts i (D.coord α i) (D.coord β i) with
      hsol | ⟨m, hm, ⟨φ⟩⟩
    · exact absurd hsol hPns
    · have : IsSimpleGroup (alternatingGroup (Fin m)) :=
        alternatingGroup.isSimpleGroup (by rwa [Nat.card_eq_fintype_card, Fintype.card_fin])
      have : IsSimpleGroup (pairProducts (D.ρ i).range (D.coord α i) (D.coord β i)) :=
        φ.isSimpleGroup
      rcases eq_bot_or_eq_of_le_of_isSimpleGroup hMP hMn with hM | hM
      · exfalso
        refine not_subsingleton_of_ne_comm hN ⟨fun a b => ?_⟩
        have h1 : ∀ x : M, x = 1 := fun x => Subtype.ext (Subgroup.mem_bot.mp (hM ▸ x.2))
        obtain ⟨x, rfl⟩ := hψ₃ a
        obtain ⟨y, rfl⟩ := hψ₃ b
        rw [h1 x, h1 y]
      · have : IsSimpleGroup M := (MulEquiv.subgroupCongr hM).isSimpleGroup
        obtain ⟨χ⟩ := nonempty_mulEquiv_of_surjective_of_ne_comm hψ₃ hN
        exact ⟨χ.symm.trans (MulEquiv.subgroupCongr hM)⟩
  · exfalso
    refine hPns ?_
    have hR := D.range_rho_of_not_isOuterFactor hSE.not_isOuterFactor
    have hle := pairProducts_le (D.ρ i).range (D.coord α i) (D.coord β i)
    rw [hR] at hle ⊢
    obtain ⟨n, k, e, hB⟩ := hSE.exists_isBenderAction
    have := hB.isSolvable_stabilizer_pair (D.coord α i) (D.coord β i)
    have hPM : pairProducts (D.M i) (D.coord α i) (D.coord β i) ≤ D.M i := fun x hx => (hle hx).1.1
    let φ : pairProducts (D.M i) (D.coord α i) (D.coord β i) →*
        stabilizer (D.M i) ({D.coord α i, D.coord β i} : Set (D.Ψc i)) :=
      (Subgroup.inclusion hPM).codRestrict _ fun x => by
        have h := hle x.2
        rw [mem_stabilizer_iff, Set.smul_set_insert, Set.smul_set_singleton]
        have ha : (Subgroup.inclusion hPM x) • D.coord α i = D.coord α i := h.1.2
        have hb : (Subgroup.inclusion hPM x) • D.coord β i = D.coord β i := h.2
        rw [ha, hb]
    refine Group.isSolvable_of_isSolvable_injective (f := φ) fun x y hxy => ?_
    have := congrArg (fun z : stabilizer (D.M i) ({D.coord α i, D.coord β i} :
      Set (D.Ψc i)) => ((z : D.M i) : Perm (D.Ψc i))) hxy
    exact Subtype.ext this

end AFLk

section KT

private theorem exists_comp_eq_of_ker_le {A B C : Type*} [Group A] [Group B] [Group C]
    {f : A →* B} (hf : Function.Surjective f) {g : A →* C} (h : f.ker ≤ g.ker) :
    ∃ g' : B →* C, ∀ a, g' (f a) = g a := by
  refine ⟨(QuotientGroup.lift f.ker g h).comp
    (QuotientGroup.quotientKerEquivOfSurjective f hf).symm.toMonoidHom, fun a => ?_⟩
  have hs : (QuotientGroup.quotientKerEquivOfSurjective f hf).symm (f a) = (a : A ⧸ f.ker) := by
    rw [MulEquiv.symm_apply_eq]
    rfl
  simp [hs]

private theorem three_le_card_of_mem' {X : Type*} {Γ : Set X} [Finite Γ] {a b c : X}
    (ha : a ∈ Γ) (hb : b ∈ Γ) (hc : c ∈ Γ) (hab : a ≠ b) (hac : a ≠ c) (hbc : b ≠ c) :
    3 ≤ Nat.card Γ := by
  rw [Nat.card_coe_set_eq, ← Set.ncard_eq_three.mpr ⟨a, b, c, hab, hac, hbc, rfl⟩]
  exact Set.ncard_le_ncard (by rintro x (rfl | rfl | rfl) <;> assumption) (Set.toFinite _)

variable {G : Type} [Group G] [Finite G] {Ω : Type} [Fintype Ω] [DecidableEq Ω] [MulAction G Ω]
  [FaithfulSMul G Ω] {α : Ω} {v : G} {hS : Sec4Setting G Ω} {C : P49Config G Ω α v}

theorem P49Config.mem_fixSet_of_le_twoPointKernel (C : P49Config G Ω α v) (hS : Sec4Setting G Ω)
    {T : Subgroup G} (hT : T ≤ twoPointKernel G Ω α C.β) :
    α ∈ fixSet Ω T ∧ C.β ∈ fixSet Ω T ∧ holtDelta G Ω α C.β ⊆ fixSet Ω T ∧
      3 ≤ Nat.card (fixSet Ω T) := by
  have hTαβ : T ≤ stabilizer G α ⊓ stabilizer G C.β := hT.trans twoPointKernel_le_inf
  have hαT : α ∈ fixSet Ω T := fun t ht => mem_stabilizer_iff.mp (Subgroup.mem_inf.mp (hTαβ ht)).1
  have hβT : C.β ∈ fixSet Ω T := fun t ht =>
    mem_stabilizer_iff.mp (Subgroup.mem_inf.mp (hTαβ ht)).2
  have hΔT : holtDelta G Ω α C.β ⊆ fixSet Ω T := fun δ hδ t ht =>
    (mem_fixingSubgroup_iff G).mp (twoPointKernel_le_fixingSubgroup (hT ht)) δ hδ
  refine ⟨hαT, hβT, hΔT, ?_⟩
  obtain ⟨δ, -, hδ, -, -⟩ := C.exists_mem_holtDelta_ne hS
  have hδα : (δ : Ω) ≠ α := fun h => left_notMem_holtDelta C.ne (h ▸ hδ)
  have hδβ : (δ : Ω) ≠ C.β := fun h => right_notMem_holtDelta C.ne (h ▸ hδ)
  exact three_le_card_of_mem' hαT hβT (hΔT hδ) C.ne (Ne.symm hδα) (Ne.symm hδβ)

theorem P49K3.exists_coord_const (K : P49K3 hS C) (hι : ∀ j, j = K.j₀) {T : Subgroup G}
    (hT2 : IsPGroup 2 T) (hTK : T ≤ twoPointKernel G Ω α C.β)
    (DT : HoltData (centralizerImage Ω T) (fixSet Ω T)) {aT bT : fixSet Ω T}
    (haT : (aT : Ω) = α) (hbT : (bT : Ω) = C.β) :
    ∃ k : DT.ι, DT.coord aT k ≠ DT.coord bT k ∧
      (∀ (δ : holtDelta G Ω α C.β) (hδ : (δ : Ω) ∈ fixSet Ω T),
        DT.coord ⟨δ, hδ⟩ k ≠ DT.coord bT k) ∧
      ∀ (δ δ' : holtDelta G Ω α C.β) (hδ : (δ : Ω) ∈ fixSet Ω T) (hδ' : (δ' : Ω) ∈ fixSet Ω T),
        δ' ∈ orbit (jOddCore (twoPointSection G Ω α C.β) (holtDelta G Ω α C.β)) δ →
          DT.coord ⟨δ, hδ⟩ k = DT.coord ⟨δ', hδ'⟩ k := by
  classical
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have h3 := C.three_le_card_holtDelta hS
  have hTαβ : T ≤ stabilizer G α ⊓ stabilizer G C.β := hTK.trans twoPointKernel_le_inf
  obtain ⟨-, -, hΔT, h3T⟩ := C.mem_fixSet_of_le_twoPointKernel hS hTK
  have hab : aT ≠ bT := fun h => C.ne (haT.symm.trans ((congrArg Subtype.val h).trans hbT))
  have hsw : longInvSwap G Ω (aT : Ω) (bT : Ω) = longInvSwap G Ω α C.β := by rw [haT, hbT]
  set J₀ := longInvSwap G Ω α C.β ∩ (Subgroup.centralizer (T : Set G) : Set G) with hJ₀
  set 𝒥 := Subgroup.closure J₀ with h𝒥
  have hJC : 𝒥 ≤ Subgroup.centralizer (T : Set G) := (Subgroup.closure_le _).mpr fun c hc => hc.2
  have hJJ : 𝒥 ≤ Subgroup.closure (longInvSwap G Ω α C.β) :=
    Subgroup.closure_mono Set.inter_subset_left
  set ψT : 𝒥 →* centralizerImage Ω T :=
    (MulAction.toPermHom (Subgroup.centralizer (T : Set G)) (fixSet Ω T)).rangeRestrict.comp
      (Subgroup.inclusion hJC) with hψT
  set ψΔ : 𝒥 →* jHull (twoPointSection G Ω α C.β) (holtDelta G Ω α C.β) :=
    (twoPointJHom hS.star α C.β).comp (Subgroup.inclusion hJJ) with hψΔ
  set 𝒥T := Subgroup.closure (longInvSwap (centralizerImage Ω T) (fixSet Ω T) aT bT) with h𝒥T
  have hgen : ∀ (x : 𝒥), (x : G) ∈ J₀ →
      (ψT x : centralizerImage Ω T) ∈ longInvSwap (centralizerImage Ω T) (fixSet Ω T) aT bT :=
    fun x hx => (hS.mem_longInvSwap_centralizerImage_iff hT2 h3T _).mpr
      ⟨x, by rw [hsw]; exact hx.1, hx.2, fun ω => rfl⟩
  have hmem : ∀ x : 𝒥, (ψT x : centralizerImage Ω T) ∈ 𝒥T := by
    have h : 𝒥T.comap ψT = ⊤ := by
      rw [eq_top_iff, ← Subgroup.closure_closure_coe_preimage, Subgroup.closure_le]
      intro x hx
      exact Subgroup.subset_closure (hgen x hx)
    exact fun x => (Subgroup.mem_comap.mp (h ▸ Subgroup.mem_top x))
  set ψT' : 𝒥 →* 𝒥T := ψT.codRestrict 𝒥T hmem with hψT'
  have hsurj : Function.Surjective ψT' := by
    rw [← MonoidHom.range_eq_top, eq_top_iff, ← Subgroup.closure_closure_coe_preimage,
      Subgroup.closure_le]
    intro u hu
    obtain ⟨c, hc, hcT, hcu⟩ := (hS.mem_longInvSwap_centralizerImage_iff hT2 h3T _).mp hu
    have hcJ : c ∈ J₀ := ⟨by rw [← hsw]; exact hc, hcT⟩
    refine ⟨⟨c, Subgroup.subset_closure hcJ⟩, Subtype.ext (Subtype.ext (Equiv.ext fun ω =>
      Subtype.ext (hcu ω).symm))⟩
  set ν₀ : 𝒥 →* Perm (K.D'.Ψc K.j₀) := (K.D'.ρ K.j₀).comp ψΔ with hν₀
  have hkerν : ψT'.ker ≤ ν₀.ker := fun x hx => by
    have h1 : ψΔ x = 1 := Subtype.ext (Subtype.ext (Equiv.ext fun δ => Subtype.ext (by
      have h := congrArg (fun π : 𝒥T => ((((π : centralizerImage Ω T) : Perm (fixSet Ω T))
        ⟨δ, hΔT δ.2⟩ : fixSet Ω T) : Ω)) (MonoidHom.mem_ker.mp hx)
      exact h)))
    rw [MonoidHom.mem_ker, hν₀, MonoidHom.comp_apply, h1, map_one]
  obtain ⟨ν, hν⟩ := exists_comp_eq_of_ker_le hsurj hkerν
  obtain ⟨δ₀, -, hδ₀, -, -⟩ := C.exists_mem_holtDelta_ne hS
  have hlong : ∀ e ∈ longInv (Perm (K.D'.Ψc K.j₀)) (K.D'.Ψc K.j₀), e ∈ ν₀.range := by
    intro e he
    obtain ⟨c₀, hc₀, hρ₀⟩ := hS.exists_mem_longInvSwap_rho_eq_of_twoPoint C.ne h3 K.D'
      (Function.update (fun j => K.D'.ρ j K.D'.tHull) K.j₀ e) fun j => by
        rcases hι j with rfl
        rw [Function.update_self]
        exact ⟨K.D'.mem_range_rho_of_alternating K.alt he, he⟩
    obtain ⟨c, hc, hcT, hcΔ⟩ := hS.exists_mem_longInvSwap_centralizer_eqOn C.ne hT2 hTαβ
      ⟨_, hδ₀⟩ hΔT hc₀ (closure_longInvSwap_le_stabilizer α C.β c₀.2)
    refine ⟨⟨c, Subgroup.subset_closure ⟨hc, hcT⟩⟩, ?_⟩
    have heq : ψΔ ⟨c, Subgroup.subset_closure ⟨hc, hcT⟩⟩ = twoPointJHom hS.star α C.β c₀ :=
      Subtype.ext (Subtype.ext (Equiv.ext fun δ => Subtype.ext (hcΔ δ δ.2)))
    rw [hν₀, MonoidHom.comp_apply, heq, hρ₀, Function.update_self]
  have hAlt : alternatingGroup (K.D'.Ψc K.j₀) ≤ ν.range := by
    have h : alternatingGroup (K.D'.Ψc K.j₀) ≤ ν₀.range :=
      (alternatingGroup_le_closure_longInvolutions (by
        rw [Nat.card_eq_fintype_card, K.card_eq]; decide)).trans
        ((Subgroup.closure_le _).mpr fun e he => hlong e he)
    intro σ hσ
    obtain ⟨x, hx⟩ := h hσ
    exact ⟨ψT' x, (hν x).trans hx⟩
  set N := alternatingGroup (K.D'.Ψc K.j₀) with hNdef
  set L : Subgroup 𝒥T := N.comap ν with hL
  have hLn : L.Normal := Subgroup.Normal.comap inferInstance ν
  set ψ : L →* N := (ν.comp L.subtype).codRestrict N fun x => x.2 with hψdef
  have hψs : Function.Surjective ψ := fun σ => by
    obtain ⟨x, hx⟩ := hAlt σ.2
    exact ⟨⟨x, show ν x ∈ N by rw [hx]; exact σ.2⟩, Subtype.ext hx⟩
  have : IsSimpleGroup N :=
    alternatingGroup.isSimpleGroup (by rw [Nat.card_eq_fintype_card, K.card_eq]; norm_num)
  have hN : ∃ a b : N, a * b ≠ b * a := by
    by_contra hno
    have hcomm : ∀ a b : N, a * b = b * a := fun a b => by
      by_contra h
      exact hno ⟨a, b, h⟩
    have h := K.D'.not_isMulCommutative_M K.j₀
    rw [K.alt] at h
    exact h ⟨⟨hcomm⟩⟩
  obtain ⟨k, hAk, h7k, ⟨χ⟩⟩ := DT.exists_mulEquiv_pairProducts aT bT hLn hN hψs
  have hAN : alternatingGroup (DT.Ψc k) ≤ (DT.ρ k).range := hAk ▸ Subgroup.map_le_range _ _
  have hs := DT.rho_mem_longInv DT.t_mem k
  have hsN : DT.ρ k ⟨DT.t, mem_jHull_of_mem_longInv DT.t_mem⟩ ∈ (DT.ρ k).range := ⟨_, rfl⟩
  have hkP : DT.coord aT k ≠ DT.coord bT k := by
    intro hk
    have hJ := longInv_perm_subset_of_alternatingGroup_le hAN hsN hs
    have hsw' : ∀ x, x ∈ swapSet (DT.ρ k).range (DT.coord aT k) (DT.coord aT k) ↔
        x ∈ longInvAt (Perm (DT.Ψc k)) (DT.Ψc k) (DT.coord aT k) :=
      fun x => ⟨fun hx => ⟨hx.2.1, hx.2.2⟩, fun hx => ⟨hJ hx.1, hx.1, hx.2⟩⟩
    have hP : pairProducts (DT.ρ k).range (DT.coord aT k) (DT.coord aT k) =
        alternatingGroup (DT.Ψc k) ⊓ stabilizer (Perm (DT.Ψc k)) (DT.coord aT k) := by
      rw [← closure_mul_longInvAt_perm_eq (DT.odd_card_Ψc k) h7k (DT.coord aT k), pairProducts]
      simp_rw [hsw']
    rw [← hk, hP] at χ
    obtain ⟨χ'⟩ := nonempty_alternatingGroup_inf_stabilizer_mulEquiv (DT.coord aT k)
    have hc := Nat.card_congr (χ.trans χ').toEquiv
    have : Nontrivial (K.D'.Ψc K.j₀) :=
      Fintype.one_lt_card_iff_nontrivial.mp (by rw [K.card_eq]; norm_num)
    have : Nontrivial (Fin (Fintype.card (DT.Ψc k) - 1)) :=
      Fin.nontrivial_iff_two_le.mpr (by omega)
    have h2N := two_mul_nat_card_alternatingGroup (α := K.D'.Ψc K.j₀)
    have h2P := two_mul_nat_card_alternatingGroup (α := Fin (Fintype.card (DT.Ψc k) - 1))
    rw [Nat.card_perm, Nat.card_eq_fintype_card (α := K.D'.Ψc K.j₀), K.card_eq] at h2N
    rw [Nat.card_perm, Nat.card_eq_fintype_card (α := Fin (Fintype.card (DT.Ψc k) - 1)),
      Fintype.card_fin] at h2P
    have hfac : (Fintype.card (DT.Ψc k) - 1).factorial = Nat.factorial 7 := by
      rw [← h2N, ← h2P, ← hc]
    have h7 : Fintype.card (DT.Ψc k) - 1 = 7 :=
      (Nat.factorial_inj (by omega)).mp hfac
    obtain ⟨m, hm⟩ := DT.odd_card_Ψc k
    omega
  refine ⟨k, hkP, ?_⟩
  set a := DT.coord aT k with ha
  set b := DT.coord bT k with hb
  set I : Set (DT.Ψc k) := ({a, b} : Set (DT.Ψc k))ᶜ with hI
  have hΔeq : holtDelta G Ω (aT : Ω) (bT : Ω) = holtDelta G Ω α C.β := by rw [haT, hbT]
  have hswapk : ∀ (u : centralizerImage Ω T)
      (hu : u ∈ longInvSwap (centralizerImage Ω T) (fixSet Ω T) aT bT),
      DT.ρ k ⟨u, mem_jHull_of_mem_longInv hu.1⟩ a = b ∧
        DT.ρ k ⟨u, mem_jHull_of_mem_longInv hu.1⟩ b = a := fun u hu => by
    constructor
    · rw [ha, hb, ← DT.coord_smul]
      exact congrArg (fun ω => DT.coord ω k) hu.2
    · rw [ha, hb, ← DT.coord_smul]
      exact congrArg (fun ω => DT.coord ω k) (smul_eq_of_mem_longInvSwap hu)
  have hcoordI : ∀ δ : holtDelta G Ω α C.β, DT.coord ⟨δ, hΔT δ.2⟩ k ∈ I := by
    intro δ
    have hδK : (⟨δ, hΔT δ.2⟩ : fixSet Ω T) ∈
        holtDelta (centralizerImage Ω T) (fixSet Ω T) aT bT :=
      (hS.mem_holtDelta_centralizerImage_iff hT2 h3T hab).mpr (by rw [hΔeq]; exact δ.2)
    obtain ⟨u, hu, huδ⟩ := hδK
    obtain ⟨hua, hub⟩ := hswapk u hu
    have huδk : DT.ρ k ⟨u, mem_jHull_of_mem_longInv hu.1⟩ (DT.coord ⟨δ, hΔT δ.2⟩ k) =
        DT.coord ⟨δ, hΔT δ.2⟩ k := by
      rw [← DT.coord_smul]
      exact congrArg (fun ω => DT.coord ω k) huδ
    simp only [hI, Set.mem_compl_iff, Set.mem_insert_iff, Set.mem_singleton_iff, not_or]
    exact ⟨fun h => hkP (by rw [← hua, ← h, huδk]), fun h => hkP (by rw [← hub, ← h, huδk])⟩
  refine ⟨fun δ hδ h => hcoordI δ (Or.inr h), ?_⟩
  have hJT : 𝒥T ≤ jHull (centralizerImage Ω T) (fixSet Ω T) :=
    Subgroup.closure_mono fun u hu => hu.1
  set φ₀ : 𝒥 →* Perm (DT.Ψc k) := (DT.ρ k).comp ((Subgroup.inclusion hJT).comp ψT') with hφ₀
  have hφ₀P : ∀ x : 𝒥, φ₀ x ∈ stabilizer (Perm (DT.Ψc k)) I := by
    have h : (stabilizer (Perm (DT.Ψc k)) I).comap φ₀ = ⊤ := by
      rw [eq_top_iff, ← Subgroup.closure_closure_coe_preimage, Subgroup.closure_le]
      intro x hx
      obtain ⟨hua, hub⟩ := hswapk _ (hgen x hx)
      rw [SetLike.mem_coe, Subgroup.mem_comap, hI, stabilizer_compl,
        mem_stabilizer_iff, Set.smul_set_insert, Set.smul_set_singleton]
      change ({DT.ρ k ⟨_, mem_jHull_of_mem_longInv (hgen x hx).1⟩ a,
        DT.ρ k ⟨_, mem_jHull_of_mem_longInv (hgen x hx).1⟩ b} : Set (DT.Ψc k)) = {a, b}
      rw [hua, hub, Set.pair_comm]
    exact fun x => Subgroup.mem_comap.mp (h ▸ Subgroup.mem_top x)
  set φ : 𝒥 →* Perm I :=
    (inducedHom φ₀.range I (by rintro _ ⟨x, rfl⟩; exact hφ₀P x)).comp φ₀.rangeRestrict with hφ
  have hφ_apply : ∀ (x : 𝒥) (p : I), ((φ x p : I) : DT.Ψc k) = φ₀ x p := fun x p => rfl
  set r : 𝒥 →* Perm (holtDelta G Ω α C.β) :=
    ((twoPointSection G Ω α C.β).subtype.comp
      (jHull (twoPointSection G Ω α C.β) (holtDelta G Ω α C.β)).subtype).comp ψΔ with hr
  set f : holtDelta G Ω α C.β → I := fun δ => ⟨DT.coord ⟨δ, hΔT δ.2⟩ k, hcoordI δ⟩ with hf
  have heq : ∀ (x : 𝒥) (δ : holtDelta G Ω α C.β), f (r x δ) = φ x (f δ) := fun x δ =>
    Subtype.ext (by
      show DT.coord ⟨_, hΔT (r x δ).2⟩ k =
        DT.ρ k ((Subgroup.inclusion hJT) (ψT' x)) (DT.coord ⟨δ, hΔT δ.2⟩ k)
      rw [← DT.coord_smul]
      rfl)
  obtain ⟨c₁, hc₁, hc₁T⟩ := hS.exists_mem_longInvSwap_centralizer C.ne hT2 hTαβ
  have hu₁ := hgen ⟨c₁, Subgroup.subset_closure ⟨hc₁, hc₁T⟩⟩ ⟨hc₁, hc₁T⟩
  set u₁ : jHull (centralizerImage Ω T) (fixSet Ω T) := ⟨_, mem_jHull_of_mem_longInv hu₁.1⟩
  have hswk : ∀ e ∈ swapSet (DT.ρ k).range a b, e ∈ φ₀.range := by
    intro e he
    obtain ⟨u, hu, hρu⟩ := DT.exists_mem_longInvSwap_rho_eq (α := aT) (β := bT)
      (Function.update (fun j => DT.ρ j u₁) k e) (fun j => by
        rcases eq_or_ne j k with rfl | hj
        · rw [Function.update_self]; exact he.1
        · rw [Function.update_of_ne hj]; exact ⟨u₁, rfl⟩) (fun j => by
        rcases eq_or_ne j k with rfl | hj
        · rw [Function.update_self]; exact he.2.1
        · rw [Function.update_of_ne hj]; exact DT.rho_mem_longInv hu₁.1 j) (fun j => by
        rcases eq_or_ne j k with rfl | hj
        · rw [Function.update_self]; exact he.2.2
        · rw [Function.update_of_ne hj, ← DT.coord_smul]
          exact congrArg (fun ω => DT.coord ω j) hu₁.2)
    obtain ⟨x, hx⟩ := hsurj ⟨u, Subgroup.subset_closure hu⟩
    refine ⟨x, ?_⟩
    rw [hφ₀, MonoidHom.comp_apply, MonoidHom.comp_apply, hx]
    exact (hρu k).trans (Function.update_self _ _ _)
  have hAab : alternatingGroup (DT.Ψc k) ⊓ stabilizer (Perm (DT.Ψc k)) a ⊓
      stabilizer (Perm (DT.Ψc k)) b ≤ φ₀.range := by
    rw [← pairProducts_eq_of_alternatingGroup_le hAN hsN hs hkP, pairProducts,
      Subgroup.closure_le]
    rintro _ ⟨e, he, e', he', rfl⟩
    exact mul_mem (hswk e he) (hswk e' he')
  have hA : alternatingGroup I ≤ φ.range := by
    intro σ hσ
    have ha' : a ∉ I := fun h => h (Set.mem_insert _ _)
    have hb' : b ∉ I := fun h => h (Set.mem_insert_of_mem _ rfl)
    have hmem : Perm.ofSubtype σ ∈ alternatingGroup (DT.Ψc k) ⊓
        stabilizer (Perm (DT.Ψc k)) a ⊓ stabilizer (Perm (DT.Ψc k)) b :=
      Subgroup.mem_inf.mpr ⟨Subgroup.mem_inf.mpr ⟨by
        rw [Perm.mem_alternatingGroup, Perm.sign_ofSubtype]; exact hσ,
        mem_stabilizer_iff.mpr (Perm.ofSubtype_apply_of_not_mem σ ha')⟩,
        mem_stabilizer_iff.mpr (Perm.ofSubtype_apply_of_not_mem σ hb')⟩
    obtain ⟨x, hx⟩ := hAab hmem
    refine ⟨x, Equiv.ext fun p => Subtype.ext ?_⟩
    rw [hφ_apply, hx, Perm.ofSubtype_apply_coe]
  have h5 : 5 ≤ Fintype.card I := by
    rw [← Nat.card_eq_fintype_card, Nat.card_coe_set_eq, hI, Set.ncard_compl,
      Set.ncard_pair hkP, Nat.card_eq_fintype_card]
    omega
  have hfs : Function.Surjective f := by
    intro p
    set δ₁ : holtDelta G Ω α C.β := ⟨_, hδ₀⟩
    by_cases hp : f δ₁ = p
    · exact ⟨δ₁, hp⟩
    obtain ⟨p', -, hp'⟩ := Finset.exists_mem_notMem_of_card_lt_card
      (s := ({f δ₁, p} : Finset I)) (t := Finset.univ)
      (by rw [Finset.card_univ]; exact Finset.card_le_two.trans_lt (by omega))
    simp only [Finset.mem_insert, Finset.mem_singleton, not_or] at hp'
    have hσ : swap (f δ₁) p' * swap (f δ₁) p ∈ alternatingGroup I := by
      rw [Perm.mem_alternatingGroup, map_mul, Perm.sign_swap hp, Perm.sign_swap
        (Ne.symm hp'.1)]
      rfl
    obtain ⟨x, hx⟩ := hA hσ
    refine ⟨r x δ₁, ?_⟩
    rw [heq, hx, Perm.mul_apply, swap_apply_left, swap_apply_of_ne_of_ne (Ne.symm hp)
      (Ne.symm hp'.2)]
  set Q := (jOddCore (twoPointSection G Ω α C.β) (holtDelta G Ω α C.β)).map
    (twoPointSection G Ω α C.β).subtype with hQ
  have hJr : jHull (twoPointSection G Ω α C.β) (holtDelta G Ω α C.β) ≤
      r.range.comap (twoPointSection G Ω α C.β).subtype := by
    rw [jHull_le_iff]
    intro π hπ
    obtain ⟨y, hy, hyπ⟩ := (hS.mem_longInv_twoPointSection_iff C.ne h3 π).mp hπ
    obtain ⟨c, hc, hcT, hcΔ⟩ := hS.exists_mem_longInvSwap_centralizer_eqOn C.ne hT2 hTαβ
      ⟨_, hδ₀⟩ hΔT hy (closure_longInvSwap_le_stabilizer α C.β (Subgroup.subset_closure hy))
    exact ⟨⟨c, Subgroup.subset_closure ⟨hc, hcT⟩⟩, Equiv.ext fun δ => Subtype.ext
      ((hcΔ δ δ.2).trans (hyπ δ).symm)⟩
  have hQr : Q ≤ r.range := by
    rintro _ ⟨o, ho, rfl⟩
    exact hJr (jOddCore_le_jHull ho)
  have hQn : ∀ x : 𝒥, ∀ q ∈ Q, r x * q * (r x)⁻¹ ∈ Q := by
    rintro x _ ⟨o, ho, rfl⟩
    refine ⟨(ψΔ x : twoPointSection G Ω α C.β) * o * (ψΔ x : twoPointSection G Ω α C.β)⁻¹,
      jOddCore_normal.conj_mem o ho _, ?_⟩
    rw [map_mul, map_mul, map_inv]
    rfl
  have hQodd : Odd (Nat.card Q) := by
    rw [hQ, Subgroup.card_map_of_injective (Subgroup.subtype_injective _)]
    exact odd_card_jOddCore
  intro δ δ' hδ hδ' hδδ'
  obtain ⟨o, rfl⟩ := hδδ'
  have h := apply_eq_of_mem_odd_normal r φ f hfs heq h5 hA hQr hQn hQodd
    (q := ((o : twoPointSection G Ω α C.β) : Perm (holtDelta G Ω α C.β))) ⟨o, o.2, rfl⟩ δ
  exact (congrArg Subtype.val h).symm

end KT

section Even

variable {G : Type} [Group G] [Finite G] {Ω : Type} [Fintype Ω] [DecidableEq Ω] [MulAction G Ω]
  [FaithfulSMul G Ω] {α : Ω} {v : G} {hS : Sec4Setting G Ω} {C : P49Config G Ω α v}

theorem P49K3.ncard_coord_le_one_of_even (K : P49K3 hS C) (hι : ∀ j, j = K.j₀)
    (hSEc : SEChainUnitary) (hT : ¬ Odd (Nat.card (twoPointKernel G Ω α C.β)))
    (p₀ : K.D'.Ψc K.j₀) :
    {δ : holtDelta G Ω α C.β | K.D'.coord δ K.j₀ = p₀}.ncard ≤ 1 := by
  classical
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨t, ht⟩ := exists_prime_orderOf_dvd_card' 2
    (even_iff_two_dvd.mp (Nat.not_odd_iff_even.mp hT))
  have ht' : orderOf (t : G) = 2 := by rw [Subgroup.orderOf_coe]; exact ht
  set T := Subgroup.zpowers (t : G) with hTdef
  have hT2 : IsPGroup 2 T := isPGroup_zpowers_of_orderOf_eq_two ht'
  have hTK : T ≤ twoPointKernel G Ω α C.β := Subgroup.zpowers_le.mpr t.2
  have hT1 : T ≠ ⊥ := fun h => by
    rw [hTdef, Subgroup.zpowers_eq_bot] at h
    rw [h, orderOf_one] at ht'
    exact absurd ht' (by decide)
  obtain ⟨hαT, hβT, hΔT, h3T⟩ := C.mem_fixSet_of_le_twoPointKernel hS hTK
  obtain ⟨DT⟩ := hS.holtData_centralizerImage hT2 hT1 h3T
  obtain ⟨k, -, hkb, hconst⟩ := K.exists_coord_const hι hT2 hTK DT (aT := ⟨α, hαT⟩)
    (bT := ⟨C.β, hβT⟩) rfl rfl
  obtain ⟨p₁, p₂, p₃, -, -, -, hF⟩ := Finset.card_eq_three.mp K.fix_three
  have hp₁ : K.D'.ρ K.j₀ ⟨C.vHat, C.vHat_mem_jHull hS⟩ p₁ = p₁ := by
    have h := congrArg (fun F : Finset (K.D'.Ψc K.j₀) => p₁ ∈ F) hF
    simpa using h
  rw [K.ncard_coord_eq p₀ p₁]
  by_contra hlt
  obtain ⟨γ, hγ, γ', hγ', hne⟩ := (Set.one_lt_ncard (Set.toFinite _)).mp (not_le.mp hlt)
  have hγ1 : K.D'.coord γ K.j₀ = p₁ := hγ
  have hγ'1 : K.D'.coord γ' K.j₀ = p₁ := hγ'
  have hγB : (γ : Ω) ∈ fixSet Ω (Subgroup.zpowers v) :=
    (K.mem_fixSet_iff hι γ).mpr (by rw [hγ1]; exact hp₁)
  have hγ'B : (γ' : Ω) ∈ fixSet Ω (Subgroup.zpowers v) :=
    (K.mem_fixSet_iff hι γ').mpr (by rw [hγ'1]; exact hp₁)
  have hk := hconst γ γ' (hΔT γ.2) (hΔT γ'.2) ((K.D'.coord_eq_iff γ γ').mp (funext fun j => by
    rcases hι j with rfl
    exact hγ1.trans hγ'1.symm))
  have hB3 : 3 ∣ (holtDelta (C.D.M C.i) (C.D.Ψc C.i) (C.D.coord C.a C.i)
      (C.D.coord C.b C.i)).ncard := by
    rw [← C.ncard_B_eq hS, K.ncard_B hι p₁]
    exact dvd_mul_right 3 _
  obtain ⟨y, hyα, -, hyβ, hyε⟩ := C.exists_mem_longInvAt_smul_eq hS hSEc hB3 ⟨γ.2, hγB⟩
    ⟨γ'.2, hγ'B⟩ fun h => hne (Subtype.ext h)
  set ε := y • (γ' : Ω) with hε
  have hy2 : y * y = 1 := mul_self_eq_one_of_mem_longInv hyα.1
  have hyγ : y • (γ : Ω) = C.β := by rw [← hyβ, smul_smul, hy2, one_smul]
  have hyε' : y • ε = γ' := by rw [hε, smul_smul, hy2, one_smul]
  have hΓ : ∀ δ ∈ ({C.β, (γ : Ω), (γ' : Ω), ε} : Set Ω), δ = C.β ∨ δ ∈ holtDelta G Ω α C.β := by
    intro δ hδ
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hδ
    rcases hδ with h | h | h | h <;> rw [h]
    exacts [Or.inl rfl, Or.inr γ.2, Or.inr γ'.2, Or.inr hyε.1]
  have hγβ : (γ : Ω) ≠ C.β := fun h => right_notMem_holtDelta C.ne (h ▸ γ.2)
  have hγ'β : (γ' : Ω) ≠ C.β := fun h => right_notMem_holtDelta C.ne (h ▸ γ'.2)
  have h3Γ : 3 ≤ Nat.card ({C.β, (γ : Ω), (γ' : Ω), ε} : Set Ω) :=
    three_le_card_of_mem' (Set.mem_insert _ _) (Set.mem_insert_of_mem _ (Set.mem_insert _ _))
      (Set.mem_insert_of_mem _ (Set.mem_insert_of_mem _ (Set.mem_insert _ _))) (Ne.symm hγβ)
      (Ne.symm hγ'β) fun h => hne (Subtype.ext h)
  have hTΓ : T ≤ fixingSubgroup G ({C.β, (γ : Ω), (γ' : Ω), ε} : Set Ω) := fun s hs =>
    (mem_fixingSubgroup_iff G).mpr fun δ hδ => by
      rcases hΓ δ hδ with rfl | h
      exacts [hβT s hs, hΔT h s hs]
  have hyΓ : y ∈ stabilizer G ({C.β, (γ : Ω), (γ' : Ω), ε} : Set Ω) :=
    mem_stabilizer_of_mul_self hy2 fun δ hδ => by
      simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hδ ⊢
      rcases hδ with h | h | h | h <;> rw [h]
      · exact Or.inr (Or.inl hyβ)
      · exact Or.inl hyγ
      · exact Or.inr (Or.inr (Or.inr rfl))
      · exact Or.inr (Or.inr (Or.inl hyε'))
  obtain ⟨c, hc, hcT, hcΓ⟩ := hS.frattini h3Γ hT2 hTΓ hyα.1 hyΓ
  have hcβ : c • C.β = γ := (hcΓ _ (Set.mem_insert _ _)).trans hyβ
  have hcγ' : c • (γ' : Ω) = ε :=
    hcΓ _ (Set.mem_insert_of_mem _ (Set.mem_insert_of_mem _ (Set.mem_insert _ _)))
  set ĉ := centralizerImageElt (Ω := Ω) hcT with hĉdef
  have hĉ : ĉ ∈ longInv (centralizerImage Ω T) (fixSet Ω T) :=
    (hS.mem_longInv_centralizerImage_iff hT2 h3T ĉ).mpr ⟨c, hc, hcT, fun ω => rfl⟩
  set ĉH : jHull (centralizerImage Ω T) (fixSet Ω T) := ⟨ĉ, mem_jHull_of_mem_longInv hĉ⟩
  have hρ2 : DT.ρ k ĉH * DT.ρ k ĉH = 1 := mul_self_eq_one_of_mem_longInv (DT.rho_mem_longInv hĉ k)
  have h1 : DT.coord ⟨γ, hΔT γ.2⟩ k = DT.ρ k ĉH (DT.coord ⟨C.β, hβT⟩ k) := by
    rw [← DT.coord_smul]
    exact congrArg (fun ω => DT.coord ω k) (Subtype.ext hcβ.symm)
  have h2 : DT.coord ⟨ε, hΔT hyε.1⟩ k = DT.ρ k ĉH (DT.coord ⟨γ', hΔT γ'.2⟩ k) := by
    rw [← DT.coord_smul]
    exact congrArg (fun ω => DT.coord ω k) (Subtype.ext hcγ'.symm)
  apply hkb ⟨ε, hyε.1⟩ (hΔT hyε.1)
  rw [h2, ← hk, h1, ← Perm.mul_apply, hρ2, Perm.one_apply]

end Even

end CFSG.Holt.H78
