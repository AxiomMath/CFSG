module

public import CFSG.CGT.T75B.FamSet
public import CFSG.CGT.Timmesfeld75.Sec4CaseIJClose
public import CFSG.CGT.Timmesfeld75.Sec4CaseIJIdent

public section

namespace CFSG.CGT.T75B

open CFSG.Open CFSG.CGT.Timmesfeld75

variable {G : Type} [Group G] [Finite G] [IsSimpleGroup G] {T T₁ T₂ : Subgroup G} {a : G}

theorem _root_.CFSG.CGT.Timmesfeld75.Sec4Hyp.le_normalizer_of_set
    (hAsc : AschbacherNoPolarInput) (h215 : Lemma215Stmt)
    (h26 : Lemma26Input) (hId : Sec4I4RootGroupInput) (hnab : ∃ a b : G, a * b ≠ b * a)
    (hind : SimpleCaseUpTo (Nat.card G)) (h : Sec4Hyp T T₁ a T₂)
    (hq : 2 * Nat.card (normIn T T₁) < Nat.card T) (h16 : Nat.card T ≠ 16)
    {S : Set (Subgroup G)} (hTS : T ∈ S) (hT₁S : T₁ ∈ S) (hT₂S : T₂ ∈ S)
    (hconj : ∀ M ∈ S, ∃ g : G, M = conjSubgroup g T)
    (hS3 : ∀ M ∈ S, M ≠ T → Sec3 T M) (hne : ∀ A ∈ S, famFS S A ≠ ⊥) :
    (⨆ M ∈ S, M) ≤ Subgroup.normalizer (sec4N T T₁ T₂ : Set G) := by
  obtain ⟨r, Ts, hinj, hrange⟩ := exists_fin_family S
  subst hrange
  set R : Subgroup G := ⨆ i, Ts i with hR
  have hsupR : (⨆ M ∈ Set.range Ts, M) = R := by rw [hR, iSup_range]
  rw [hsupR]
  obtain ⟨i₀, hi₀⟩ : T ∈ Set.range Ts := hTS
  obtain ⟨j₁, hj₁⟩ : T₁ ∈ Set.range Ts := hT₁S
  obtain ⟨j₂, hj₂⟩ : T₂ ∈ Set.range Ts := hT₂S
  have hr : 0 < r := Nat.pos_of_ne_zero fun h => by subst h; exact i₀.elim0
  have hTR : T ≤ R := hi₀ ▸ le_iSup Ts i₀
  have hT₁R : T₁ ≤ R := hj₁ ▸ le_iSup Ts j₁
  have hT₂R : T₂ ≤ R := hj₂ ▸ le_iSup Ts j₂
  have hRconj : ∀ i, ∃ g ∈ R, Ts i = conjSubgroup g T := by
    intro i
    by_cases hMT : Ts i = T
    · exact ⟨1, R.one_mem, hMT.trans (conjSubgroup_one T).symm⟩
    · obtain ⟨y, hy, hy'⟩ := (hS3 _ (Set.mem_range_self i) hMT).conj
      exact ⟨y, sup_le hTR (le_iSup Ts i) hy, hy'⟩
  have hne' : ∀ j, (⨅ i, normIn (Ts j) (Ts i)) ≠ ⊥ := fun j => by
    rw [famF_eq_famFS rfl j]
    exact hne _ (Set.mem_range_self j)
  have hq' : ∃ j, 2 * Nat.card ↥(normIn T (Ts j)) < Nat.card T := ⟨j₁, by rw [hj₁]; exact hq⟩
  obtain ⟨hsimple, -, hhyp, -, -, hker⟩ := jLemma h215 h26 hnab hind h.pair.wc h.glob h.iso h16 hr hinj
    (fun i => hconj _ (Set.mem_range_self i)) ⟨i₀, hi₀⟩ hne' (R := R) rfl hRconj hq'
  have hYR : sec4Y T T₁ T₂ ≤ R := sup_le (sup_le hTR hT₁R) hT₂R
  obtain ⟨y₁, hy₁Y, hy₁⟩ := h.exists_mem_sec4Y_conj₁
  obtain ⟨y₂, hy₂Y, hy₂⟩ := h.exists_mem_sec4Y_conj₂
  have hy₁R : y₁ ∈ R := hYR hy₁Y
  have hy₂R : y₂ ∈ R := hYR hy₂Y
  let ψ : ↥(sec4Y T T₁ T₂) →* jQuot ↥R := (jMap ↥R).comp (Subgroup.inclusion hYR)
  have hψ : ∀ y : ↥(sec4Y T T₁ T₂), ψ y = 1 → Sec4ActsTriv T T₁ T₂ (y : G) := by
    intro y hy
    have hw : Subgroup.inclusion hYR y ∈ (jMap ↥R).ker := MonoidHom.mem_ker.2 hy
    refine h.actsTriv_of_commutators (fun t ht => ?_) (fun t ht => ?_) (fun t ht => ?_)
    · exact normIn_le_sec4N_left (comm_mem_normIn_of_mem_ker_jMap h.pair.wc hTR R.one_mem hy₁R
        (conjSubgroup_one T).symm hy₁ hw ht)
    · exact normIn_le_sec4N_mid (comm_mem_normIn_of_mem_ker_jMap h.pair.wc hTR hy₁R R.one_mem
        hy₁ (conjSubgroup_one T).symm hw ht)
    · exact normIn_le_sec4N_right (comm_mem_normIn_of_mem_ker_jMap h.pair.wc hTR hy₂R R.one_mem
        hy₂ (conjSubgroup_one T).symm hw ht)
  obtain ⟨f, hf, ρ, hρ⟩ := h.exists_surjective_psu3_range hAsc hq ψ hψ
  have hrange := range_comp_inclusion_eq_sup (jMap ↥R) rfl hYR hy₁R hy₂R hy₁ hy₂
  have htop : ψ.range = ⊤ := hId (jQuot ↥R) ((T.subgroupOf R).map (jMap ↥R)) hhyp ψ.range
    (jMap ↥R ⟨y₁, hy₁R⟩) (jMap ↥R ⟨y₂, hy₂R⟩) hrange f hf ⟨ρ, hρ⟩
  intro r' hr'
  have hmem : jMap ↥R ⟨r', hr'⟩ ∈ ψ.range := htop ▸ Subgroup.mem_top _
  obtain ⟨y, hy⟩ := hmem
  have hw : (Subgroup.inclusion hYR y)⁻¹ * ⟨r', hr'⟩ ∈ (jMap ↥R).ker := by
    rw [MonoidHom.mem_ker, map_mul, map_inv]
    have h1 : (jMap ↥R) (Subgroup.inclusion hYR y) = jMap ↥R ⟨r', hr'⟩ := hy
    rw [h1]
    simp
  have hwn := fun i => mem_normalizer_of_conjSubgroup_eq (hker _ hw i)
  have hw' : (((Subgroup.inclusion hYR y)⁻¹ * ⟨r', hr'⟩ : ↥R) : G) ∈
      Subgroup.normalizer (sec4N T T₁ T₂ : Set G) :=
    sec4N_normalizer_of_normalizes (hi₀ ▸ hwn i₀) (hj₁ ▸ hwn j₁) (hj₂ ▸ hwn j₂)
  have e1 : r' = (y : G) * (((Subgroup.inclusion hYR y)⁻¹ * ⟨r', hr'⟩ : ↥R) : G) := by
    show r' = (y : G) * ((y : G)⁻¹ * r')
    group
  rw [e1]
  exact (Subgroup.normalizer _).mul_mem (h.sec4Y_le_normalizer y.2) hw'

end CFSG.CGT.T75B
