module

public import CFSG.CGT.Timmesfeld75.Sec4CaseIJClose
public import CFSG.CGT.Timmesfeld75.Sec4CaseIProps
public import CFSG.CGT.Timmesfeld75.Sec4CaseIJFamily
public import CFSG.CGT.Timmesfeld75.Sec4CaseIJIdent

public section

namespace CFSG.CGT.Timmesfeld75

open CFSG.Open
open scoped commutatorElement

section Main

variable {G : Type} [Group G] [Finite G] [IsSimpleGroup G] {T T₁ T₂ T₃ : Subgroup G} {a x : G}

theorem Sec4Ext.false_of_inputs
    (hAsc : AschbacherNoPolarInput) (h215 : Lemma215Stmt)
    (h26 : Lemma26Input) (hId : Sec4I4RootGroupInput) (hnab : ∃ a b : G, a * b ≠ b * a)
    (hind : SimpleCaseUpTo (Nat.card G)) (hq : 2 * Nat.card (normIn T T₁) < Nat.card T)
    (h16 : Nat.card T ≠ 16) (e : Sec4Ext T T₁ T₂ a x T₃) : False := by
  have h := e.hyp
  obtain ⟨y₁, hy₁Y, hy₁⟩ := h.exists_mem_sec4Y_conj₁
  obtain ⟨y₂, hy₂Y, hy₂⟩ := h.exists_mem_sec4Y_conj₂
  obtain ⟨c₃, hc₃, hc₃eq⟩ := e.exists_conj₃
  set R : Subgroup G := ⨆ i, sec4Fam T T₁ T₂ T₃ i with hR
  have hTR : T ≤ R := le_iSup (sec4Fam T T₁ T₂ T₃) 0
  have hT₁R : T₁ ≤ R := le_iSup (sec4Fam T T₁ T₂ T₃) 1
  have hT₂R : T₂ ≤ R := le_iSup (sec4Fam T T₁ T₂ T₃) 2
  have hT₃R : T₃ ≤ R := le_iSup (sec4Fam T T₁ T₂ T₃) 3
  have hYR : sec4Y T T₁ T₂ ≤ R := sup_le (sup_le hTR hT₁R) hT₂R
  have hy₁R : y₁ ∈ R := hYR hy₁Y
  have hy₂R : y₂ ∈ R := hYR hy₂Y
  have hc₃R : c₃ ∈ R := (sup_le hTR hT₃R) hc₃
  have hRconj : ∀ i, ∃ g ∈ R, sec4Fam T T₁ T₂ T₃ i = conjSubgroup g T := by
    intro i
    fin_cases i
    · exact ⟨1, R.one_mem, (conjSubgroup_one T).symm⟩
    · exact ⟨y₁, hy₁R, hy₁⟩
    · exact ⟨y₂, hy₂R, hy₂⟩
    · exact ⟨c₃, hc₃R, hc₃eq⟩
  obtain ⟨hsimple, -, hhyp, -, -, hker⟩ := jLemma h215 h26 hnab hind h.pair.wc h.glob h.iso h16
    (by norm_num) e.fam_injective (fun i => (hRconj i).imp fun _ hg => hg.2) ⟨0, rfl⟩
    e.fam_ne_bot rfl hRconj ⟨1, hq⟩
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
  have hRN : R ≤ Subgroup.normalizer (sec4N T T₁ T₂ : Set G) := by
    intro r hr
    have hmem : jMap ↥R ⟨r, hr⟩ ∈ ψ.range := htop ▸ Subgroup.mem_top _
    obtain ⟨y, hy⟩ := hmem
    have hw : (Subgroup.inclusion hYR y)⁻¹ * ⟨r, hr⟩ ∈ (jMap ↥R).ker := by
      rw [MonoidHom.mem_ker, map_mul, map_inv]
      have h1 : (jMap ↥R) (Subgroup.inclusion hYR y) = jMap ↥R ⟨r, hr⟩ := hy
      rw [h1]
      simp
    have hwn := fun i => mem_normalizer_of_conjSubgroup_eq (hker _ hw i)
    have hw' : (((Subgroup.inclusion hYR y)⁻¹ * ⟨r, hr⟩ : ↥R) : G) ∈
        Subgroup.normalizer (sec4N T T₁ T₂ : Set G) :=
      sec4N_normalizer_of_normalizes (hwn 0) (hwn 1) (hwn 2)
    have e1 : r = (y : G) * (((Subgroup.inclusion hYR y)⁻¹ * ⟨r, hr⟩ : ↥R) : G) := by
      show r = (y : G) * ((y : G)⁻¹ * r)
      group
    rw [e1]
    exact (Subgroup.normalizer _).mul_mem (h.sec4Y_le_normalizer y.2) hw'
  have hle := conjSubgroup_le_sec4Y_of_mem_normalizer hAsc h hq (hRN hc₃R)
  rw [← hc₃eq] at hle
  exact e.notle hle

end Main

theorem sec4I4TrivialAction_of_inputs
    (hAsc : AschbacherNoPolarInput) (h215 : Lemma215Stmt)
    (h26 : Lemma26Input) (hId : Sec4I4RootGroupInput) : Sec4I4TrivialAction := by
  intro G _ _ _ hnab hind T T₁ T₂ a h hq h16 x hxD hxT hx
  obtain ⟨g, t, ht, ht1, hxg⟩ := hxD
  have hxT₃ : x ∈ conjSubgroup g⁻¹ T := mem_conjSubgroup.2 (by
    rw [inv_inv, hxg]
    have e : g * (g⁻¹ * t * g) * g⁻¹ = t := by group
    rw [e]
    exact ht)
  by_cases hle : conjSubgroup g⁻¹ T ≤ sec4Y T T₁ T₂
  · exact h.mem_sec4N_of_conj_le hxT₃ hle hx
  · exfalso
    have hx1 : x ≠ 1 := classD_ne_one (T := T) ⟨g, t, ht, ht1, hxg⟩
    exact Sec4Ext.false_of_inputs hAsc h215 h26 hId hnab hind hq h16
      ⟨h, ⟨g⁻¹, rfl⟩, hxT₃, hx1, hxT, hx, hle⟩

end CFSG.CGT.Timmesfeld75
