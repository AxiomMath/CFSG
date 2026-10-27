module

public import CFSG.LieType.SeitzGeneration.OrthBlocks

public section

namespace CFSG.LieType.SeitzGeneration.OrthBlk

open Module QuadraticMap CFSG.ClassicalGroups.Orthogonal

section Pair

theorem exists_indep_pair {G : Type*} [Group G] {p : ℕ} (hp : p.Prime) (hexp : ∀ x : G, x ^ p = 1)
    (N : Subgroup G) [N.Normal] (hN : p < N.index) :
    ∃ a b : G, a ∉ N ∧ ∀ i j : ℕ, a ^ i * b ^ j ∈ N → p ∣ i ∧ p ∣ j := by
  have : Fact p.Prime := ⟨hp⟩
  have hcard : Nat.card (G ⧸ N) = N.index := rfl
  have hexpQ : ∀ x : G ⧸ N, x ^ p = 1 := by
    intro x
    obtain ⟨y, rfl⟩ := QuotientGroup.mk_surjective x
    rw [← QuotientGroup.mk_pow, hexp y, QuotientGroup.mk_one]
  have hfin : Finite (G ⧸ N) := Nat.finite_of_card_ne_zero (by rw [hcard]; have := hp.pos; omega)
  obtain ⟨a', ha'⟩ : ∃ a' : G ⧸ N, a' ≠ 1 := by
    by_contra h
    push Not at h
    have : Subsingleton (G ⧸ N) := ⟨fun x y => by rw [h x, h y]⟩
    have h1 : Nat.card (G ⧸ N) = 1 := Nat.card_eq_one_iff_unique.mpr ⟨this, ⟨1⟩⟩
    have := hp.one_lt
    omega
  have hord : orderOf a' = p := orderOf_eq_prime (hexpQ a') ha'
  obtain ⟨b', hb'⟩ : ∃ b' : G ⧸ N, b' ∉ Subgroup.zpowers a' := by
    by_contra h
    push Not at h
    have htop : Subgroup.zpowers a' = ⊤ := eq_top_iff.mpr fun x _ => h x
    have h2 : Nat.card (Subgroup.zpowers a') = Nat.card (G ⧸ N) := by
      rw [htop, Subgroup.card_top]
    rw [Nat.card_zpowers, hord, hcard] at h2
    omega
  have hb1 : b' ≠ 1 := fun h => hb' (h ▸ Subgroup.one_mem _)
  have hordb : orderOf b' = p := orderOf_eq_prime (hexpQ b') hb1
  obtain ⟨a, rfl⟩ := QuotientGroup.mk_surjective a'
  obtain ⟨b, rfl⟩ := QuotientGroup.mk_surjective b'
  refine ⟨a, b, fun h => ha' ((QuotientGroup.eq_one_iff a).mpr h), fun i j hij => ?_⟩
  have h1 : (a : G ⧸ N) ^ i * (b : G ⧸ N) ^ j = 1 := by
    rw [← QuotientGroup.mk_pow, ← QuotientGroup.mk_pow, ← QuotientGroup.mk_mul]
    exact (QuotientGroup.eq_one_iff _).mpr hij
  have hbj : (b : G ⧸ N) ^ j = ((a : G ⧸ N) ^ i)⁻¹ := eq_inv_of_mul_eq_one_right h1
  have hj : p ∣ j := by
    by_contra hj
    have hcop : Nat.Coprime j (orderOf (b : G ⧸ N)) := by
      rw [hordb]
      exact ((Nat.Prime.coprime_iff_not_dvd hp).mpr hj).symm
    obtain ⟨m, hm⟩ := exists_pow_eq_self_of_coprime hcop
    apply hb'
    rw [← hm, hbj]
    exact Subgroup.pow_mem _ (Subgroup.inv_mem _ (Subgroup.pow_mem _ (Subgroup.mem_zpowers _) i)) m
  refine ⟨?_, hj⟩
  have hbj1 : (b : G ⧸ N) ^ j = 1 := by
    rw [← hordb] at hj
    exact orderOf_dvd_iff_pow_eq_one.mp hj
  rw [hbj1, mul_one] at h1
  rw [← hord]
  exact orderOf_dvd_iff_pow_eq_one.mpr h1

end Pair

section Family

variable {K V : Type} [Field K] [AddCommGroup V] [Module K V] {Q : QuadraticForm K V} {p : ℕ}

@[expose] def OrthSep (Q : QuadraticForm K V) (S T : Submodule K V) : Prop :=
  ∀ s ∈ S, ∀ t ∈ T, polar Q s t = 0

theorem OrthSep.symm {S T : Submodule K V} (h : OrthSep Q S T) : OrthSep Q T S :=
  fun t ht s hs => by rw [polar_comm]; exact h s hs t ht

structure BlockFamily (Q : QuadraticForm K V) (p : ℕ) (T : Submodule K V)
    (L : List (Submodule K V × (V ≃ₗ[K] V))) : Prop where
  le : ∀ x ∈ L, x.1 ≤ T
  reg : ∀ x ∈ L, PolarNondegOn Q x.1
  block : ∀ x ∈ L, IsBlock Q p x.1 x.2
  orth : L.Pairwise fun x y => OrthSep Q x.1 y.1

theorem BlockFamily.nil (T : Submodule K V) : BlockFamily Q p T [] :=
  ⟨fun _ h => by simp at h, fun _ h => by simp at h, fun _ h => by simp at h, List.Pairwise.nil⟩

theorem BlockFamily.single {T S : Submodule K V} {g : V ≃ₗ[K] V} (hST : S ≤ T)
    (hS : PolarNondegOn Q S) (hg : IsBlock Q p S g) : BlockFamily Q p T [(S, g)] :=
  ⟨fun x hx => by rw [List.mem_singleton.mp hx]; exact hST,
    fun x hx => by rw [List.mem_singleton.mp hx]; exact hS,
    fun x hx => by rw [List.mem_singleton.mp hx]; exact hg, List.pairwise_singleton _ _⟩

theorem BlockFamily.append {T₁ T₂ : Submodule K V} {L₁ L₂ : List (Submodule K V × (V ≃ₗ[K] V))}
    (h₁ : BlockFamily Q p T₁ L₁) (h₂ : BlockFamily Q p T₂ L₂) (hT : OrthSep Q T₁ T₂) :
    BlockFamily Q p (T₁ ⊔ T₂) (L₁ ++ L₂) where
  le x hx := by
    rcases List.mem_append.mp hx with hx | hx
    · exact (h₁.le x hx).trans le_sup_left
    · exact (h₂.le x hx).trans le_sup_right
  reg x hx := by
    rcases List.mem_append.mp hx with hx | hx
    · exact h₁.reg x hx
    · exact h₂.reg x hx
  block x hx := by
    rcases List.mem_append.mp hx with hx | hx
    · exact h₁.block x hx
    · exact h₂.block x hx
  orth := List.pairwise_append.mpr ⟨h₁.orth, h₂.orth, fun x hx y hy s hs t ht =>
    hT s (h₁.le x hx hs) t (h₂.le y hy ht)⟩

structure ElemAbOrth (Q : QuadraticForm K V) (p : ℕ) (F : Subgroup (V ≃ₗ[K] V)) : Prop where
  orth : ∀ a ∈ F, a ∈ TauCeti.QuadraticMap.orthogonalGroup Q
  pow : ∀ a ∈ F, a ^ p = 1
  comm : ∀ a ∈ F, ∀ b ∈ F, a * b = b * a

@[expose] def FStable (F : Subgroup (V ≃ₗ[K] V)) (S : Submodule K V) : Prop :=
  ∀ a ∈ F, ∀ s ∈ S, a s ∈ S

theorem relIndex_le_prime (hp : p.Prime) (hpK : (p : K) ≠ 0) {F : Subgroup (V ≃ₗ[K] V)}
    (hF : ElemAbOrth Q p F) {S : Submodule K V} (hFS : FStable F S)
    (hbase : ∀ a ∈ F, (∃ s ∈ S, a s ≠ s) → ∀ c ∈ S, a c = c → c = 0) :
    (stabPW S).relIndex F ≤ p := by
  by_contra hlt
  push Not at hlt
  let N : Subgroup F := (stabPW S).subgroupOf F
  have hNidx : N.index = (stabPW S).relIndex F := rfl
  have : N.Normal := ⟨fun n hn g => by
    have hc : g * n = n * g := Subtype.ext (hF.comm g g.2 n n.2)
    rw [hc, mul_assoc, mul_inv_cancel, mul_one]
    exact hn⟩
  obtain ⟨a, b, haN, hab⟩ := exists_indep_pair hp (fun x : F => Subtype.ext (hF.pow x x.2)) N
    (by rw [hNidx]; exact hlt)
  have hcomm : Commute (a : V ≃ₗ[K] V) (b : V ≃ₗ[K] V) := hF.comm a a.2 b b.2
  have hS := eq_zero_of_fixedPointFree_plane hp hpK hcomm (hF.pow a a.2) (hF.pow b b.2)
    (fun s hs => hFS a a.2 s hs) (fun s hs => hFS b b.2 s hs) (by
      intro i j hij s hs hfix
      have hg : (a ^ i * b ^ j : F) ∉ N := fun h => hij (hab i j h)
      have hg' : ¬ ∀ s ∈ S, ((a ^ i * b ^ j : F) : V ≃ₗ[K] V) s = s := hg
      push Not at hg'
      obtain ⟨s', hs', hs'ne⟩ := hg'
      exact hbase _ (a ^ i * b ^ j : F).2 ⟨s', hs', hs'ne⟩ s hs hfix)
  exact haN (fun s hs => by rw [hS s hs, map_zero])

theorem exists_blockFamily [FiniteDimensional K V] (hp : p.Prime) (hpK : (p : K) ≠ 0)
    {F : Subgroup (V ≃ₗ[K] V)} (hF : ElemAbOrth Q p F) :
    ∀ (n : ℕ) (S : Submodule K V), finrank K S = n → PolarNondegOn Q S → FStable F S →
      ∃ L, BlockFamily Q p S L ∧ (stabPW S).relIndex F ≤ p ^ L.length := by
  intro n
  induction n using Nat.strong_induction_on with
  | _ n ih =>
    intro S hn hS hFS
    by_cases hmix : ∃ a ∈ F, (∃ s ∈ S, a s ≠ s) ∧ ∃ c ∈ S, c ≠ 0 ∧ a c = c
    · obtain ⟨a, haF, ⟨s, hsS, hsa⟩, c, hcS, hc0, hac⟩ := hmix
      have haO := hF.orth a haF
      have hap := hF.pow a haF
      have haS : ∀ s ∈ S, a s ∈ S := fun s hs => hFS a haF s hs
      have hCB : fixIn a S ⊔ normKer a p S = S := sup_fixIn_normKer hap hpK haS
      have hdisj := disjoint_fixIn_normKer (g := a) (p := p) hpK S
      have regC := polarNondegOn_fixIn haO hap hpK hS haS
      have regB := polarNondegOn_normKer haO hap hpK hS haS
      have hCst : FStable F (fixIn a S) := fun b hb v hv =>
        fixIn_stable (hF.comm a haF b hb) (fun s hs => hFS b hb s hs) v hv
      have hBst : FStable F (normKer a p S) := fun b hb v hv =>
        normKer_stable (hF.comm a haF b hb) (fun s hs => hFS b hb s hs) v hv
      obtain ⟨c₀, hc₀, b₀, hb₀, hsum⟩ := exists_add_fixIn_normKer hap hpK haS hsS
      have hb₀0 : b₀ ≠ 0 := by
        rintro rfl
        rw [add_zero] at hsum
        exact hsa (hsum ▸ (mem_fixIn.mp hc₀).2)
      have hCS : fixIn a S < S := by
        refine lt_of_le_of_ne inf_le_left fun h => ?_
        have hb₀S : b₀ ∈ S := (mem_normKer.mp hb₀).1
        have hb₀C : b₀ ∈ fixIn a S := by rw [h]; exact hb₀S
        exact hb₀0 (Submodule.disjoint_def.mp hdisj b₀ hb₀C hb₀)
      have hBS : normKer a p S < S := by
        refine lt_of_le_of_ne inf_le_left fun h => ?_
        have hcC : c ∈ fixIn a S := mem_fixIn.mpr ⟨hcS, hac⟩
        have hcB : c ∈ normKer a p S := by rw [h]; exact hcS
        exact hc0 (Submodule.disjoint_def.mp hdisj c hcC hcB)
      obtain ⟨L₁, hL₁, hi₁⟩ := ih (finrank K (fixIn a S))
        (hn ▸ Submodule.finrank_lt_finrank_of_lt hCS) (fixIn a S) rfl regC hCst
      obtain ⟨L₂, hL₂, hi₂⟩ := ih (finrank K (normKer a p S))
        (hn ▸ Submodule.finrank_lt_finrank_of_lt hBS) (normKer a p S) rfl regB hBst
      have horth : OrthSep Q (fixIn a S) (normKer a p S) := fun u hu w hw =>
        polar_fixIn_normKer haO hpK (mem_fixIn.mp hu).2 (mem_normKer.mp hw).2
      refine ⟨L₁ ++ L₂, hCB ▸ hL₁.append hL₂ horth, ?_⟩
      rw [← hCB, stabPW_sup, List.length_append, pow_add]
      exact (Subgroup.relIndex_inf_le).trans (Nat.mul_le_mul hi₁ hi₂)
    · have hbase : ∀ a ∈ F, (∃ s ∈ S, a s ≠ s) → ∀ c ∈ S, a c = c → c = 0 := by
        intro a haF hmove c hcS hac
        by_contra hc0
        exact hmix ⟨a, haF, hmove, c, hcS, hc0, hac⟩
      by_cases hfix : F ≤ stabPW S
      · exact ⟨[], BlockFamily.nil S, by
          rw [Subgroup.relIndex_eq_one.mpr hfix]; simp⟩
      · obtain ⟨a, haF, hna⟩ := Set.not_subset.mp hfix
        have hmove : ∃ s ∈ S, a s ≠ s := by
          by_contra h
          push Not at h
          exact hna h
        have h1 : ∀ s ∈ S, a s ∈ S := fun s hs => hFS a haF s hs
        have h2 : ∀ s ∈ S, a.symm s ∈ S := fun s hs => hFS a⁻¹ (F.inv_mem haF) s hs
        refine ⟨[(S, extendId hS a h1 h2)], BlockFamily.single le_rfl hS
          (extendId_isBlock hS (hF.orth a haF) (hF.pow a haF) h1 h2 hmove), ?_⟩
        simpa using relIndex_le_prime hp hpK hF hFS hbase

theorem exists_blockFamily_top [FiniteDimensional K V] (hQ : (polarBilin Q).Nondegenerate)
    (hp : p.Prime) (hpK : (p : K) ≠ 0) {F : Subgroup (V ≃ₗ[K] V)} (hF : ElemAbOrth Q p F) :
    ∃ L, BlockFamily Q p ⊤ L ∧ Nat.card F ≤ p ^ L.length := by
  obtain ⟨L, hL, hidx⟩ := exists_blockFamily hp hpK hF _ ⊤ rfl (polarNondegOn_top hQ)
    (fun _ _ _ _ => Submodule.mem_top)
  refine ⟨L, hL, ?_⟩
  rw [stabPW_top, Subgroup.relIndex_bot_left] at hidx
  exact hidx

end Family

end CFSG.LieType.SeitzGeneration.OrthBlk
