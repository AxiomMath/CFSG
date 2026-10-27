module

public import Mathlib.GroupTheory.SpecificGroups.Alternating.Simple
public import CFSG.LocalAnalysis.OddStandard.HigherRank.YamadaG23.Lit.LitE16

public section

namespace CFSG.OddStandard.HigherRank.YamadaG23

open MulAction

theorem lit_card_alt6 : Nat.card (alternatingGroup (Fin 6)) = 360 := by
  rw [nat_card_alternatingGroup, Nat.card_eq_fintype_card, Fintype.card_fin]
  decide

theorem lit_isSimpleGroup_alt6 : IsSimpleGroup (alternatingGroup (Fin 6)) :=
  alternatingGroup.isSimpleGroup (by simp)

theorem lit_orbit_ne_five {S : Type*} [Finite S] [MulAction (alternatingGroup (Fin 6)) S]
    (s : S) : (orbit (alternatingGroup (Fin 6)) s).ncard ≠ 5 := by
  intro h5
  haveI := lit_isSimpleGroup_alt6
  set H := stabilizer (alternatingGroup (Fin 6)) s with hH
  have hidx : H.index = 5 := by rw [hH, index_stabilizer, h5]
  haveI : H.FiniteIndex := ⟨by omega⟩
  have hdvd := Subgroup.index_normalCore_dvd_factorial_index H
  rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal H.normalCore with hb | ht
  · rw [hb, Subgroup.index_bot, lit_card_alt6, hidx] at hdvd
    have := Nat.le_of_dvd (Nat.factorial_pos 5) hdvd
    simp [Nat.factorial] at this
  · have : H = ⊤ := top_le_iff.mp (ht ▸ H.normalCore_le)
    rw [this, Subgroup.index_top] at hidx
    omega

theorem lit_subtypePerm_pow {α : Type*} (f : Equiv.Perm α) {p : α → Prop}
    (hf : ∀ x, p (f x) ↔ p x) (k : ℕ) (x : {x // p x}) :
    (((f.subtypePerm hf) ^ k) x : α) = (f ^ k) x := by
  induction k generalizing x with
  | zero => simp
  | succ k ih =>
    rw [pow_succ, pow_succ, Equiv.Perm.mul_apply, Equiv.Perm.mul_apply, ih]
    rfl

theorem lit_five_dvd_orbit {K S : Type*} [Group K] [Finite S] [MulAction K S] {k : K}
    (hk : k ^ 5 = 1) (hfree : ∀ s : S, k • s ≠ s) (s : S) : 5 ∣ Nat.card (orbit K s) := by
  have hp : ∀ x : S, x ∈ orbit K s ↔ (toPermHom K S k) x ∈ orbit K s := by
    intro x
    constructor
    · rintro ⟨g, rfl⟩
      exact ⟨k * g, by simp [mul_smul]⟩
    · rintro ⟨g, hg⟩
      refine ⟨k⁻¹ * g, ?_⟩
      have hg' : g • s = k • x := hg
      show (k⁻¹ * g) • s = x
      rw [mul_smul, hg', inv_smul_smul]
  let σ : Equiv.Perm {x // x ∈ orbit K s} := (toPermHom K S k).subtypePerm
    (fun x => (hp x).symm)
  have hσ : σ ^ 5 = 1 := by
    ext x
    rw [lit_subtypePerm_pow]
    have : (toPermHom K S k) ^ 5 = 1 := by rw [← map_pow, hk, map_one]
    rw [this]
    rfl
  have h := lit_card_modEq_fix σ hσ
  have h0 : Nat.card {a // σ a = a} = 0 := by
    rw [Nat.card_eq_zero]
    left
    refine ⟨fun a => ?_⟩
    apply hfree a.1.1
    have := congrArg Subtype.val a.2
    exact this
  rw [h0] at h
  exact Nat.modEq_zero_iff_dvd.mp h

theorem lit_alt6_orbit_univ {S : Type*} [Finite S] [MulAction (alternatingGroup (Fin 6)) S]
    (hS : Nat.card S = 15) {k : alternatingGroup (Fin 6)} (hk : orderOf k = 5)
    (hfree : ∀ s : S, k • s ≠ s) (s : S) : orbit (alternatingGroup (Fin 6)) s = Set.univ := by
  have hk5 : k ^ 5 = 1 := hk ▸ pow_orderOf_eq_one k
  have hbig : ∀ t : S, 10 ≤ Nat.card (orbit (alternatingGroup (Fin 6)) t) := by
    intro t
    have h1 := lit_five_dvd_orbit hk5 hfree t
    have h2 := lit_orbit_ne_five t
    rw [← Nat.card_coe_set_eq] at h2
    haveI : Nonempty (orbit (alternatingGroup (Fin 6)) t) := ⟨⟨t, mem_orbit_self t⟩⟩
    have h3 : 0 < Nat.card (orbit (alternatingGroup (Fin 6)) t) := Nat.card_pos
    omega
  by_contra hne
  obtain ⟨t, ht⟩ := (Set.ne_univ_iff_exists_notMem _).mp hne
  have hdisj : Disjoint (orbit (alternatingGroup (Fin 6)) s)
      (orbit (alternatingGroup (Fin 6)) t) := by
    rw [Set.disjoint_left]
    intro x hxs hxt
    apply ht
    have h1 : orbit (alternatingGroup (Fin 6)) x = orbit (alternatingGroup (Fin 6)) s :=
      orbit_eq_iff.mpr hxs
    have h2 : orbit (alternatingGroup (Fin 6)) x = orbit (alternatingGroup (Fin 6)) t :=
      orbit_eq_iff.mpr hxt
    rw [← h1, h2]
    exact mem_orbit_self t
  have hs := hbig s
  have ht' := hbig t
  have hunion := Set.ncard_union_eq hdisj (Set.toFinite _) (Set.toFinite _)
  have hle := Set.ncard_le_card ((orbit (alternatingGroup (Fin 6)) s) ∪
    (orbit (alternatingGroup (Fin 6)) t))
  rw [Nat.card_coe_set_eq] at hs ht'
  omega

theorem lit_alt6_transitive {P S : Type*} [Group P] [Finite S] (hS : Nat.card S = 15)
    (ρ : P →* Equiv.Perm S) (ψ : P →* alternatingGroup (Fin 6)) (hψ : Function.Surjective ψ)
    (hker : ∀ g, ψ g = 1 → ρ g = 1) {n : P} (hn : orderOf (ψ n) = 5)
    (hfree : ∀ s, ρ n s ≠ s) : ∀ s s' : S, ∃ g : P, ρ g s = s' := by
  have hle : ψ.ker ≤ ρ.ker := fun g hg => hker g hg
  let ρ' : alternatingGroup (Fin 6) →* Equiv.Perm S :=
    ψ.liftOfRightInverse (Function.surjInv hψ) (Function.rightInverse_surjInv hψ) ⟨ρ, hle⟩
  have hρ' : ∀ g, ρ' (ψ g) = ρ g := fun g =>
    MonoidHom.liftOfRightInverse_comp_apply ψ (Function.surjInv hψ)
      (Function.rightInverse_surjInv hψ) ⟨ρ, hle⟩ g
  letI : MulAction (alternatingGroup (Fin 6)) S := MulAction.compHom S ρ'
  intro s s'
  have horb := lit_alt6_orbit_univ hS hn (fun t => by
    have : (ψ n) • t = ρ n t := by
      show ρ' (ψ n) t = ρ n t
      rw [hρ']
    rw [this]
    exact hfree t) s
  have hmem : s' ∈ orbit (alternatingGroup (Fin 6)) s := horb ▸ Set.mem_univ s'
  obtain ⟨k, hk⟩ := hmem
  obtain ⟨g, rfl⟩ := hψ k
  refine ⟨g, ?_⟩
  have : (ψ g) • s = s' := hk
  rw [← this]
  show ρ g s = ρ' (ψ g) s
  rw [hρ']

theorem lit_toPerm_apply {V : Type*} [Group V] (f : MulAut V) (v : V) :
    MulAut.toPerm V f v = f v := rfl

theorem lit_free_mulAut {V : Type*} [Group V] [Finite V] (hV : Nat.card V = 16) (f : MulAut V)
    (h5 : f ^ 5 = 1) (hnt : f ≠ 1) : ∀ v : V, f v = v → v = 1 := by
  let F : Subgroup V := MonoidHom.eqLocus f.toMonoidHom (MonoidHom.id V)
  have hmem : ∀ v : V, v ∈ F ↔ MulAut.toPerm V f v = v := fun v => Iff.rfl
  have hσ : MulAut.toPerm V f ^ 5 = 1 := by rw [← map_pow, h5, map_one]
  have hcard : Nat.card F ≡ 16 [MOD 5] := by
    have h := lit_card_modEq_fix (MulAut.toPerm V f) hσ
    rw [hV] at h
    have e : Nat.card F = Nat.card {a // MulAut.toPerm V f a = a} :=
      Nat.card_congr (Equiv.subtypeEquivRight hmem)
    rw [e]
    exact h.symm
  have hdvd : Nat.card F ∣ 16 := hV ▸ Subgroup.card_subgroup_dvd_card F
  have hF1 : Nat.card F = 1 := by
    rcases lit_one_or_sixteen hdvd (hcard.trans (by decide)) with h | h
    · exact h
    · exfalso
      apply hnt
      have htop : F = ⊤ := Subgroup.eq_top_of_card_eq F (by rw [h, hV])
      ext v
      have : v ∈ F := htop ▸ Subgroup.mem_top _
      exact (hmem v).mp this
  have hbot : F = ⊥ := Subgroup.card_eq_one.mp hF1
  intro v hv
  have : v ∈ F := (hmem v).mpr hv
  rwa [hbot, Subgroup.mem_bot] at this

theorem lit_alt6_transitive_group {P V : Type*} [Group P] [Group V] [Finite V]
    (hV : Nat.card V = 16) (ρ : P →* MulAut V) (ψ : P →* alternatingGroup (Fin 6))
    (hψ : Function.Surjective ψ) (hker : ∀ g, ψ g = 1 ↔ ρ g = 1) :
    ∀ v w : V, v ≠ 1 → w ≠ 1 → ∃ g : P, ρ g v = w := by
  haveI : Fact (Nat.Prime 5) := ⟨Nat.prime_five⟩
  obtain ⟨k, hk⟩ := exists_prime_orderOf_dvd_card' (G := alternatingGroup (Fin 6)) 5
    (by rw [lit_card_alt6]; norm_num)
  obtain ⟨n, rfl⟩ := hψ k
  have hn5 : ρ n ^ 5 = 1 := by
    rw [← map_pow]
    refine (hker _).mp ?_
    rw [map_pow]
    exact hk ▸ pow_orderOf_eq_one _
  have hnt : ρ n ≠ 1 := fun h => by
    have := (hker n).mpr h
    rw [this, orderOf_one] at hk
    omega
  have hfree := lit_free_mulAut hV (ρ n) hn5 hnt
  have hS : Nat.card {v : V // v ≠ 1} = 15 := by
    classical
    haveI := Fintype.ofFinite V
    rw [Nat.card_eq_fintype_card, Fintype.card_subtype_compl (fun v : V => v = 1),
      Fintype.card_subtype_eq, ← Nat.card_eq_fintype_card, hV]
  have hstab : ∀ (g : P) (v : V), (MulAut.toPerm V (ρ g)) v ≠ 1 ↔ v ≠ 1 := fun g v => by
    rw [lit_toPerm_apply]
    exact (ρ g).map_ne_one_iff
  let ρ'' : P →* Equiv.Perm {v : V // v ≠ 1} :=
    { toFun := fun g => Equiv.Perm.subtypePerm (p := fun v : V => v ≠ 1)
        (MulAut.toPerm V (ρ g)) (hstab g)
      map_one' := by
        ext v
        simp [lit_toPerm_apply]
      map_mul' := fun g h => by
        ext v
        simp [lit_toPerm_apply] }
  intro v w hv hw
  obtain ⟨g, hg⟩ := lit_alt6_transitive hS ρ'' ψ hψ
    (fun g hg => by
      ext v
      simp [ρ'', (hker g).mp hg])
    hk (fun s hs => s.2 (hfree s.1 (congrArg Subtype.val hs))) ⟨v, hv⟩ ⟨w, hw⟩
  exact ⟨g, congrArg Subtype.val hg⟩

end CFSG.OddStandard.HigherRank.YamadaG23
