module

public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.Setup.LayerNilpD
public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.Setup.LayerNilpC

public section

namespace CFSG.QuasithinUnique.Setup.Layer

open CFSG.QuasithinUnique.Setup.Offender CFSG.Quasithin.B6
open scoped commutatorElement

universe v

variable {k : Type*} [Field k] {V : Type v} [AddCommGroup V] [Module k V]

namespace OddAbelianSetting

variable [CharP k 2] [Finite V] {G N A : Subgroup (V ≃ₗ[k] V)} {ι : Type*}
  {g : ι → V ≃ₗ[k] V} [Fintype ι] (h : OddAbelianSetting G N A) (F : ConjFamily G N A g)
  {Fn : Subgroup (V ≃ₗ[k] V)} (hF : OverGroup G Fn N)

include h F hF

theorem normalizes_S {f : V ≃ₗ[k] V} (hf : f ∈ Fn) (i : ι) :
    conjSub f (natS N A g i) = natS N A g i ∧ conjSub f (natL N A g i) = natL N A g i := by
  have hfG : f ∈ G := hF.le_G hf
  obtain ⟨j, hjS, hjL, -⟩ := h.S_perm F hfG i
  suffices hji : j = i by
    subst hji
    exact ⟨hjS, hjL⟩
  by_contra hji
  have pd := h.planeData_family F i
  obtain ⟨a, ha, ha1⟩ := h.exists_ne_one_A F i
  have haS : a ∈ natS N A g i := (le_sup_right : natA A g i ≤ natS N A g i) ha
  have haG : a ∈ G := h.natB_le (h.S_le_B F i haS)
  have htS : f * a * f⁻¹ ∈ natS N A g j := hjS ▸ conjSub_mem_of_mem haS
  have hnormF : ∀ x ∈ G, ∀ y ∈ Fn, x * y * x⁻¹ ∈ Fn := fun x hx y hy =>
    (Subgroup.mem_normalizer_iff.1
      ((Subgroup.normal_subgroupOf_iff_le_normalizer hF.le_G).1 hF.normal hx) y).1 hy
  have huF : f * a * f⁻¹ * a⁻¹ ∈ Fn := by
    have e : f * a * f⁻¹ * a⁻¹ = f * (a * f⁻¹ * a⁻¹) := by group
    rw [e]
    exact Fn.mul_mem hf (hnormF a haG f⁻¹ (Fn.inv_mem hf))
  have huB : f * a * f⁻¹ * a⁻¹ ∈ natB G N A :=
    (natB G N A).mul_mem (h.S_le_B F j htS) ((natB G N A).inv_mem (h.S_le_B F i haS))
  have huD := h.odd_mem_D F hF.odd huB huF
  obtain ⟨l, hl, hul⟩ := h.D_act F i _ huD
  obtain ⟨hW, -⟩ := h.S_action F i
  have hla : l * a = 1 := by
    have hlaS : l * a ∈ natS N A g i :=
      (natS N A g i).mul_mem ((le_sup_left : natL N A g i ≤ natS N A g i) hl) haS
    refine h.S_ext F i hlaS (Subgroup.one_mem _) (fun w hw => ?_)
    have h1 : (f * a * f⁻¹) w = w := h.S_fix_I F hji hw _ htS
    have haw : a w ∈ natI N A g i := hW a haS w hw
    have h2 := hul (a w) haw
    have h3 : (f * a * f⁻¹ * a⁻¹) (a w) = (f * a * f⁻¹) w := by
      show (f * a * f⁻¹) (a⁻¹ (a w)) = (f * a * f⁻¹) w
      rw [gl_inv_apply]
    show l (a w) = w
    rw [← h2, h3, h1]
  have hal : a = l⁻¹ := eq_inv_of_mul_eq_one_right hla
  have haL : a ∈ natL N A g i := by
    rw [hal]
    exact (natL N A g i).inv_mem hl
  have hdis : Disjoint (natL N A g i) (natA A g i) :=
    Subgroup.disjoint_of_coprime_natCard (by rw [pd.card_L, pd.card_A]; norm_num)
  exact ha1 (Subgroup.disjoint_def.1 hdis haL ha)

theorem centralizes_L {f : V ≃ₗ[k] V} (hf : f ∈ Fn) (i : ι) :
    ∀ x ∈ natL N A g i, f * x = x * f := by
  have : Finite (V ≃ₗ[k] V) := finite_linearEquiv
  have pd := h.planeData_family F i
  have e := (h.normalizes_S F hF hf i).2
  have hnorm : f ∈ Subgroup.normalizer (natL N A g i : Set (V ≃ₗ[k] V)) := by
    refine mem_normalizer_of_conjSub_le (le_of_eq e) ?_
    have : conjSub f⁻¹ (natL N A g i) = natL N A g i := by
      calc conjSub f⁻¹ (natL N A g i) = conjSub f⁻¹ (conjSub f (natL N A g i)) := by rw [e]
        _ = natL N A g i := conjSub_inv_conjSub _ _
    exact le_of_eq this
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have hcyc : IsCyclic (natL N A g i) := isCyclic_of_prime_card pd.card_L
  let ψ := (natL N A g i).normalizerMonoidHom ⟨f, hnorm⟩
  have h2 : orderOf ψ ∣ 2 := by
    have := orderOf_dvd_natCard ψ
    rwa [IsCyclic.card_mulAut, pd.card_L,
      show Nat.totient 3 = 2 from rfl] at this
  have hoddf : Odd (orderOf f) := by
    have h1 : orderOf (⟨f, hf⟩ : ↥Fn) ∣ Nat.card Fn := orderOf_dvd_natCard _
    rw [Subgroup.orderOf_mk] at h1
    exact Odd.of_dvd_nat hF.odd h1
  have h3 : orderOf ψ ∣ orderOf f := by
    have := orderOf_map_dvd (Subgroup.normalizerMonoidHom (natL N A g i)) ⟨f, hnorm⟩
    rwa [Subgroup.orderOf_mk] at this
  have hψ1 : orderOf ψ = 1 := by
    have hodd' : Odd (orderOf ψ) := Odd.of_dvd_nat hoddf h3
    rcases (Nat.dvd_prime Nat.prime_two).1 h2 with h4 | h4
    · exact h4
    · rw [h4] at hodd'
      exact absurd hodd' (by decide)
  have hψ : ψ = 1 := orderOf_eq_one_iff.1 hψ1
  intro x hx
  have e1 : ψ ⟨x, hx⟩ = ⟨x, hx⟩ := by
    rw [hψ]
    rfl
  have e2 : f * x * f⁻¹ = x := congrArg Subtype.val e1
  exact mul_inv_eq_iff_eq_mul.1 e2

theorem acts_via_L {f : V ≃ₗ[k] V} (hf : f ∈ Fn) (i : ι) :
    ∃ l ∈ natL N A g i, ∀ w ∈ natI N A g i, f w = l w := by
  have pd := h.planeData_family F i
  have fd := h.famData F
  have hcomm := h.centralizes_L F hF hf i
  have hinv : ∀ w ∈ natI N A g i, f w ∈ natI N A g i := fun w hw =>
    map_mem_commSub_top_of_commute (MonoidHom.id (V ≃ₗ[k] V)) (natL N A g i)
      (fun l hl => hcomm l hl) hw
  have hmap : (natI N A g i).map (f : V →ₗ[k] V) = natI N A g i := by
    refine submodule_eq_of_le_of_card_ge ?_ (natCard_map_linearEquiv f (natI N A g i)).ge
    rintro _ ⟨w, hw, rfl⟩
    exact hinv w hw
  let m : ↥(natI N A g i) ≃ₗ[k] ↥(natI N A g i) :=
    LinearEquiv.ofSubmodules f (natI N A g i) (natI N A g i) hmap
  obtain ⟨hW, hbij⟩ := h.S_action F i
  obtain ⟨s, hs⟩ := hbij.2 m
  have hsf : ∀ w ∈ natI N A g i, (s : V ≃ₗ[k] V) w = f w := by
    intro w hw
    have e1 := resSub_apply (MonoidHom.id (V ≃ₗ[k] V)) (natS N A g i) (natI N A g i) hW s ⟨w, hw⟩
    rw [hs] at e1
    exact e1.symm
  have hsS : (s : V ≃ₗ[k] V) ∈ natS N A g i := s.2
  obtain ⟨l', hl', a', ha', hs'⟩ := mem_sup_mul pd.A_norm hsS
  have hsx : ∀ x ∈ natL N A g i, (s : V ≃ₗ[k] V) * x = x * s := by
    intro x hx
    have hxS : x ∈ natS N A g i := (le_sup_left : natL N A g i ≤ natS N A g i) hx
    refine h.S_ext F i ((natS N A g i).mul_mem hsS hxS) ((natS N A g i).mul_mem hxS hsS)
      (fun w hw => ?_)
    have hxw : x w ∈ natI N A g i := hW x hxS w hw
    show (s : V ≃ₗ[k] V) (x w) = x ((s : V ≃ₗ[k] V) w)
    rw [hsf _ hxw, hsf w hw]
    exact congrArg (fun e : V ≃ₗ[k] V => e w) (hcomm x hx)
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have hLc : ∀ x ∈ natL N A g i, ∀ y ∈ natL N A g i, x * y = y * x :=
    cyclic_comm (isCyclic_of_prime_card (p := 3) pd.card_L)
  have ha'1 : a' = 1 := by
    by_contra ha1
    refine h.not_centralizes_A F i ha' ha1 (fun x hx => ?_)
    have h1 : a' = l'⁻¹ * s := by rw [hs']; group
    have h2 : (s : V ≃ₗ[k] V) * x = x * s := hsx x hx
    have h3 : l'⁻¹ * x = x * l'⁻¹ := hLc l'⁻¹ ((natL N A g i).inv_mem hl') x hx
    calc a' * x = l'⁻¹ * (s * x) := by rw [h1]; group
      _ = l'⁻¹ * (x * s) := by rw [h2]
      _ = (l'⁻¹ * x) * s := by group
      _ = (x * l'⁻¹) * s := by rw [h3]
      _ = x * (l'⁻¹ * s) := by group
      _ = x * a' := by rw [h1]
  refine ⟨l', hl', fun w hw => ?_⟩
  rw [← hsf w hw, hs', ha'1, mul_one]

end OddAbelianSetting

end CFSG.QuasithinUnique.Setup.Layer
