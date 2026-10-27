module

public import CFSG.LocalAnalysis.ComponentClassification.HSFLitKD8cC9
public import CFSG.LocalAnalysis.ComponentClassification.HSFLitKD8cExcl
public import Certificates.Certificate22801

public section

namespace CFSG.ComponentClassification.HSFLit

open CFSG Subgroup

namespace KD8c

open KD7 KD8ab Sec8

variable {X : Type} [Group X] [Finite X] {t : X} {L : Subgroup X} {A : L2Data t L}
  {C : A.CaseKD} {S : KDBase A C} {T₁ : Subgroup X}

theorem s_10_60 : chi0B 10 (sR 6 0) = false := by decide +kernel

namespace Conf

namespace T2

namespace Lift

variable {K : Conf S T₁} {T : K.T2} (W : T.Lift)

theorem card_PC2 (x y : Ext W.D') :
    Nat.card ((T.P ⊓ centralizer ({W.ψ x} : Set X)) ⊓ centralizer ({W.ψ y} : Set X) :
      Subgroup X) = cntCC x y := by
  classical
  have hb : Function.Bijective (fun g : {g : Ext W.D' // g * x = x * g ∧ g * y = y * g} =>
      (⟨W.ψ g.1, ⟨W.ψ_mem _, mem_centralizer_singleton_iff.mpr
        (by rw [← map_mul, g.2.1, map_mul])⟩, mem_centralizer_singleton_iff.mpr
        (by rw [← map_mul, g.2.2, map_mul])⟩ :
      ((T.P ⊓ centralizer ({W.ψ x} : Set X)) ⊓ centralizer ({W.ψ y} : Set X) : Subgroup X))) := by
    refine ⟨fun a b h => Subtype.ext (W.ψ_injective ?_), fun g => ?_⟩
    · have := congrArg Subtype.val h
      simpa using this
    · obtain ⟨g, ⟨hgP, hgx⟩, hgy⟩ := g
      obtain ⟨z, rfl⟩ := W.exists_ψ hgP
      refine ⟨⟨z, W.ψ_injective ?_, W.ψ_injective ?_⟩, rfl⟩
      · rw [map_mul, map_mul]; exact mem_centralizer_singleton_iff.mp hgx
      · rw [map_mul, map_mul]; exact mem_centralizer_singleton_iff.mp hgy
  rw [← Nat.card_eq_of_bijective _ hb, Nat.card_eq_fintype_card, Fintype.card_subtype]
  rfl

theorem mem_cent_Zx_iff {g : X} : g ∈ centralizer (K.Zx : Set X) ↔
    S.z * g = g * S.z ∧ S.k * g = g * S.k := by
  constructor
  · intro h
    refine ⟨mem_centralizer_iff.mp h _ ?_, mem_centralizer_iff.mp h _ ?_⟩
    · rw [← K.ι_z]; exact ⟨MC.z, mem_Zh.mpr (by decide +kernel), rfl⟩
    · rw [← K.ι_k]; exact ⟨MC.k, mem_Zh.mpr (by decide +kernel), rfl⟩
  · rintro ⟨hz, hk⟩
    rw [mem_centralizer_iff]
    rintro _ ⟨a, ha, rfl⟩
    have hz' : K.ι MC.z * g = g * K.ι MC.z := by rw [K.ι_z]; exact hz
    have hk' : K.ι MC.k * g = g * K.ι MC.k := by rw [K.ι_k]; exact hk
    rcases List.mem_cons.mp ((inZ_iff a).mp ha) with rfl | h
    · simp
    rcases List.mem_cons.mp h with rfl | h
    · exact hz'
    rcases List.mem_cons.mp h with rfl | h
    · exact hk'
    rcases List.mem_cons.mp h with rfl | h
    · rw [map_mul, mul_assoc, hk', ← mul_assoc, hz', mul_assoc]
    · exact absurd h (List.not_mem_nil)

theorem card_PC3 (x : Ext W.D') :
    Nat.card (T.P ⊓ centralizer (insert (W.ψ x) (K.Zx : Set X)) : Subgroup X) =
      (Finset.univ.filter fun g : Ext W.D' => g * x = x * g ∧
        g * Ext.incl W.D' MC.z = Ext.incl W.D' MC.z * g ∧
        g * Ext.incl W.D' MC.k = Ext.incl W.D' MC.k * g).card := by
  classical
  have hmem : ∀ g : Ext W.D', W.ψ g ∈ centralizer (insert (W.ψ x) (K.Zx : Set X)) ↔
      (g * x = x * g ∧ g * Ext.incl W.D' MC.z = Ext.incl W.D' MC.z * g ∧
        g * Ext.incl W.D' MC.k = Ext.incl W.D' MC.k * g) := by
    intro g
    have hins : W.ψ g ∈ centralizer (insert (W.ψ x) (K.Zx : Set X)) ↔
        W.ψ x * W.ψ g = W.ψ g * W.ψ x ∧ W.ψ g ∈ centralizer (K.Zx : Set X) := by
      simp only [mem_centralizer_iff, Set.mem_insert_iff, forall_eq_or_imp, SetLike.mem_coe]
    rw [hins, mem_cent_Zx_iff (K := K), ← K.ι_z, ← K.ι_k, ← W.ψ_incl, ← W.ψ_incl, ← map_mul,
      ← map_mul, ← map_mul, ← map_mul, ← map_mul, ← map_mul]
    constructor
    · rintro ⟨h1, h2, h3⟩
      exact ⟨(W.ψ_injective h1).symm, (W.ψ_injective h2).symm, (W.ψ_injective h3).symm⟩
    · rintro ⟨h1, h2, h3⟩
      exact ⟨by rw [h1], by rw [h2], by rw [h3]⟩
  have hb : Function.Bijective (fun g : {g : Ext W.D' // g * x = x * g ∧
      g * Ext.incl W.D' MC.z = Ext.incl W.D' MC.z * g ∧
      g * Ext.incl W.D' MC.k = Ext.incl W.D' MC.k * g} =>
      (⟨W.ψ g.1, W.ψ_mem _, (hmem g.1).mpr g.2⟩ :
        (T.P ⊓ centralizer (insert (W.ψ x) (K.Zx : Set X)) : Subgroup X))) := by
    refine ⟨fun a b h => Subtype.ext (W.ψ_injective ?_), fun g => ?_⟩
    · have := congrArg Subtype.val h
      simpa using this
    · obtain ⟨g, hgP, hgc⟩ := g
      obtain ⟨z, rfl⟩ := W.exists_ψ hgP
      exact ⟨⟨z, (hmem z).mp hgc⟩, rfl⟩
  rw [← Nat.card_eq_of_bijective _ hb, Nat.card_eq_fintype_card, Fintype.card_subtype]

theorem false_of_checkE2 [IsSimpleGroup X] (hnonab : ∃ a b : X, a * b ≠ b * a) {bs : ℕ}
    {qb : Bool} {reps c9 : List ℕ} {tab : ℕ} {χ : Ext W.D' →* Multiplicative (ZMod 2)}
    (hχ : ∀ x, χ x = if chiB bs qb x then Multiplicative.ofAdd 1 else 1)
    (hc9 : ∀ r ∈ c9, ¬ ConjTo t (W.ψ (ofCodeE r)))
    (hc : checkE2 W.D' bs qb reps c9 tab = true) : False := by
  simp only [checkE2, Bool.and_eq_true, decide_eq_true_eq, List.all_eq_true, Bool.or_eq_true]
    at hc
  obtain ⟨⟨⟨hu64, hu⟩, hreps⟩, hall⟩ := hc
  refine W.false_of_ext hnonab χ hu64 ((W.chi_ne_one hχ _).mpr hu) fun x hx2 hx64 hx => ?_
  by_cases hx1 : x = 1
  · rw [hx1, map_one]
    exact fun ⟨c, hc⟩ => L2K.t_ne_one (A := A) (by
      calc t = c⁻¹ * (c * t * c⁻¹) * c := by group
        _ = 1 := by rw [hc]; group)
  have hne : chiB bs qb x ≠ chiB bs qb W.uh := by
    intro h
    apply hx
    rw [hχ, hχ, h]
  have hr := hall x hx2 hx1 hne
  set r := conjE tab x * x * (conjE tab x)⁻¹ with hrdef
  have hrc := hreps _ hr
  refine W.nt_conj (conjE tab x) x ?_
  rw [← hrdef]
  have hcc : ccE r = ccE x := ccE_conj _ _
  rcases hrc with ((hs | hcc64) | hcnt) | h9
  · rw [ofCodeE_codeE] at hs
    exact W.nt_seed (fun _ => K.not_conjTo_w₂) hs
  · rw [ofCodeE_codeE] at hcc64
    exact W.nt_card (by omega)
  · rw [ofCodeE_codeE] at hcnt
    exact W.nt_cnt (by omega) hu64 hcnt
  · have := hc9 _ h9
    rwa [ofCodeE_codeE] at this

theorem c9_of_check {rc wz wk wzk utab : ℕ} {c9 : List (ℕ × ℕ)} (hu64 : 64 ≤ ccE W.uh)
    (hc : checkC9 W.D' rc wz wk wzk utab c9 = true) :
    ∀ p ∈ c9, ¬ ConjTo t (W.ψ (ofCodeE p.1)) := by
  simp only [checkC9, Bool.and_eq_true, decide_eq_true_eq, List.all_eq_true] at hc
  obtain ⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨hR2, hR1⟩, hRc⟩, hnorm⟩, hcA⟩, hsq⟩, hwz⟩, hwk⟩, hwzk⟩, hU⟩, hpairs⟩ := hc
  set Rh : Ext W.D' := ofCodeE rc with hRh
  have hZx : ∀ y : Ext W.D', inZE y = true → W.ψ y ∈ K.Zx := by
    intro y hy
    simp only [inZE, Bool.and_eq_true, Bool.not_eq_eq_eq_not, Bool.not_true] at hy
    rw [W.ψ_e0 hy.1]
    exact ⟨y.a, hy.2, rfl⟩
  intro p hp
  obtain ⟨⟨h64, hcomm⟩, h16⟩ := hpairs p hp
  refine W.not_conjTo_of_C9 (R := W.ψ Rh) (W.ψ_mem _) (by rw [← map_mul, hR2, map_one])
    (fun h => hR1 (W.ψ_injective (h.trans (map_one _).symm))) ((W.card_PC _).trans hRc)
    ?_ ((W.card_PC3 _).trans hcA) ?_ ?_ ((W.card_PC _).symm ▸ hu64) ?_
    (h := W.ψ (ofCodeE p.1)) ((W.card_PC _).symm ▸ h64) (c := W.ψ (ofCodeE p.2))
    (W.ψ_mem _) ?_ ?_
  · intro g hg
    obtain ⟨gh, rfl⟩ := W.exists_ψ hg
    have := hZx _ (hnorm gh)
    rwa [map_mul, map_mul, map_mul, map_inv, map_inv] at this
  · intro x hx hx4
    obtain ⟨xh, rfl⟩ := W.exists_ψ hx.1
    have hxc : xh * Rh = Rh * xh :=
      W.ψ_injective (by rw [map_mul, map_mul]; exact mem_centralizer_singleton_iff.mp hx.2)
    have hx4' : xh * xh * (xh * xh) = 1 :=
      W.ψ_injective (by simpa only [map_mul, map_one] using hx4)
    have := hZx _ (hsq xh hxc hx4')
    rwa [map_mul] at this
  · intro z hz
    obtain ⟨a, ha, rfl⟩ := hz
    have hmemR : ∀ w : Ext W.D', w * Rh = Rh * w →
        W.ψ w ∈ T.P ⊓ centralizer ({W.ψ Rh} : Set X) := fun w hw =>
      ⟨W.ψ_mem _, mem_centralizer_singleton_iff.mpr (by rw [← map_mul, hw, map_mul])⟩
    rcases List.mem_cons.mp ((inZ_iff a).mp ha) with rfl | h
    · exact ⟨1, one_mem _, by simp⟩
    rcases List.mem_cons.mp h with rfl | h
    · exact ⟨_, hmemR _ hwz.1, by rw [← map_mul, hwz.2, W.ψ_incl]⟩
    rcases List.mem_cons.mp h with rfl | h
    · exact ⟨_, hmemR _ hwk.1, by rw [← map_mul, hwk.2, W.ψ_incl]⟩
    rcases List.mem_cons.mp h with rfl | h
    · exact ⟨_, hmemR _ hwzk.1, by rw [← map_mul, hwzk.2, W.ψ_incl]⟩
    · exact absurd h List.not_mem_nil
  · intro g hg hg2 hg1 hg16
    obtain ⟨gh, rfl⟩ := W.exists_ψ hg.1
    have hgc : gh * W.uh = W.uh * gh :=
      W.ψ_injective (by rw [map_mul, map_mul]; exact mem_centralizer_singleton_iff.mp hg.2)
    have hg2' : gh * gh = 1 := W.ψ_injective (by rw [map_mul, map_one]; exact hg2)
    have hg1' : gh ≠ 1 := fun h => hg1 (by rw [h, map_one])
    rw [W.card_PC2] at hg16
    rcases hU gh hgc hg2' hg1' hg16 with hbig | hconj
    · left
      rw [W.card_PC]
      exact hbig
    · right
      exact W.conjTo_of_conj_eq hconj
  · rw [← map_inv, ← map_mul, ← map_mul]
    exact mem_centralizer_singleton_iff.mpr
      (by rw [← map_mul, ← map_mul, hcomm.symm, map_mul, map_mul])
  · rw [← map_inv, ← map_mul, ← map_mul, W.card_PC2]
    exact h16


theorem false_of_cert60 [IsSimpleGroup X] (hnonab : ∃ a b : X, a * b ≠ b * a) (W : T.Lift)
    (hj : W.j = 6) (hi : W.i = 0) : False := by
  have hc := Certificates.certificate22801
  obtain ⟨j, i, hj3, hj4, Q, hQ, hs, hQm, hQn, hcs⟩ := W
  simp only at hj hi
  subst hj hi
  let W : T.Lift := ⟨6, 0, hj3, hj4, Q, hQ, hs, hQm, hQn, hcs⟩
  simp only [chk60, Bool.and_eq_true] at hc
  obtain ⟨χ₀, hχ₀⟩ := exists_chi0 10 pcx_10 nf_10
  obtain ⟨χ, hχ⟩ := exists_chi hj3 hj4 0 10 false hχ₀ phi_10_6 s_10_60
  have hE : checkE2 W.D' 10 false [1, 2, 4, 8, 16, 260, 279] [279] tab60 = true := hc.1
  have hC9 : checkC9 W.D' 198 34 17 96 utab60 [(279, 0)] = true := hc.2
  have hu64 : 64 ≤ ccE W.uh := by
    simp only [checkE2, Bool.and_eq_true, decide_eq_true_eq] at hE
    exact hE.1.1.1
  have h9 := W.c9_of_check hu64 hC9
  exact W.false_of_checkE2 hnonab hχ (fun r hr => by
    simp only [List.mem_singleton] at hr
    subst hr
    exact h9 (279, 0) (by simp)) hE

end Lift

end T2

end Conf

end KD8c

end CFSG.ComponentClassification.HSFLit
