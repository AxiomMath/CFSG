module

public import CFSG.GH74.GLS.Stage2.Bender.Thm1.P67Stmt
public import CFSG.GH74.GLS.Stage2.Bender.Thm1.P67Fit
public import CFSG.GH74.GLS.Stage2.Bender.Thm1.P67Comp
public import CFSG.GH74.Generic.Sections
public import CFSG.GH74.GLS.Stage2.Bender.Thm1.Prop67

public section

namespace CFSG.GH74.GLS.Stage2.Bender.Thm1

open Subgroup CFSG CFSG.GH74 CFSG.GH74.GLS CFSG.Blueprint CFSG.Assembly.LowTwoRank
  CFSG.GH74.GLS.Stage12 CFSG.GH74.GLS.Stage2.Local CFSG.GH74.GLS.Bg
open scoped commutatorElement

theorem prop6_7E_of_cf67 (h : CF67) : Prop6_7E := by
  intro G _ _ z k S M p hC r V hr hV hVe hVc hv X hX hX1 hVX N hN hXN
  by_contra hEM
  obtain ⟨K, hKc, hKM⟩ := exists_component_not_le hEM
  have : Fact r.Prime := ⟨hr⟩
  have hNtop : N ≠ ⊤ := hN.1
  have hVF : V ≤ Fm M := (hV.trans inf_le_left).trans (Op_le_Fm r hr M)
  have hrodd : Odd r := by
    have h1 : Nat.card ↥V ∣ Nat.card ↥(Fm M) := Subgroup.card_dvd_of_le hVF
    rw [hVc] at h1
    have h2 : Odd (r * r) := by
      rw [← pow_two]; exact Odd.of_dvd_nat (odd_card_Fm hC.hyp hC.mem) h1
    exact (Nat.odd_mul.mp h2).1
  have hVX' : V ≤ normalizer (X : Set G) := le_sup_left.trans hVX
  have hVN : V ≤ N := hVX'.trans hXN
  have hZX : Zr r M ≤ centralizer (X : Set G) :=
    Subgroup.le_centralizer_iff.mp (hX.trans (Fm_le_centralizer_Zr hr M))
  have hZN : Zr r M ≤ N := hZX.trans ((Subgroup.centralizer_le_normalizer _).trans hXN)
  have hZM : normalizer ((Zr r M : Subgroup G) : Set G) = M := normalizer_Zr hC hr
  let V' : Subgroup ↥N := V.subgroupOf N
  let Z' : Subgroup ↥N := (Zr r M).subgroupOf N
  have hVe' : IsElementaryAbelian r ↥V' := IsElementaryAbelian.subgroupOf hVN
  have hVc' : Nat.card ↥V' = r ^ 2 := by
    rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe hVN).toEquiv]; exact hVc
  have hZcard : Nat.card ↥Z' = Nat.card ↥(Zr r M) :=
    Nat.card_congr (Subgroup.subgroupOfEquivOfLe hZN).toEquiv
  have hZab : ∀ a ∈ Z', ∀ b ∈ Z', a * b = b * a := fun a ha b hb =>
    Subtype.ext (Zr_comm r M a ha b hb)
  have hZodd : Odd (Nat.card ↥Z') := by rw [hZcard]; exact Zr_odd hC r
  have hZcop : Nat.Coprime (Nat.card ↥Z') r := by rw [hZcard]; exact Zr_coprime hr M
  have hcomm : ∀ v ∈ V', ∀ w ∈ Z', v * w = w * v := by
    intro v hv' w hw'
    have h1 : (v : G) ∈ Op r M := (hV.trans inf_le_left) hv'
    have h2 : (w : G) ∈ Ep r M := Zr_le_Ep r M hw'
    have h3 := Subgroup.mem_centralizer_iff.mp
      ((Subgroup.commutator_eq_bot_iff_le_centralizer.mp (commute_Op_Ep r hr M)) h1) (w : G) h2
    exact Subtype.ext h3.symm
  have hcard : Nat.card (CFSG.LocalCores.ComponentIndex ↥N) ≤ 2 :=
    card_componentIndex_le_two (SectionalTwoRankLE.subgroup N hC.ctx.std.gen4)
  have hodd_norm : ∀ A : Subgroup ↥N, Odd (Nat.card ↥A) → A ≤ normalizer (K : Set ↥N) := by
    intro A hA a ha
    exact mem_normalizer_of_odd_orderOf hcard
      (Odd.of_dvd_nat hA (Subgroup.orderOf_dvd_natCard A ha)) hKc
  have hVodd : Odd (Nat.card ↥V') := by rw [hVc']; exact hrodd.pow
  have hVnorm : V' ≤ normalizer (K : Set ↥N) := hodd_norm V' hVodd
  have hZnorm : Z' ≤ normalizer (K : Set ↥N) := hodd_norm Z' hZodd
  have hCvM : ∀ v : G, v ∈ V → v ≠ 1 → centralizer ({v} : Set G) ≤ M := fun v hvV hv1 =>
    (cen_le_normalizer_zpowers_aux v).trans (hv v hvV hv1).2.2.2
  have hfaith : ∀ v ∈ V', v ≠ 1 → ¬ K ≤ centralizer ({v} : Set ↥N) := by
    intro v hv' hv1 hKv
    apply hKM
    rintro _ ⟨c, hc, rfl⟩
    refine hCvM (v : G) hv' (fun h => hv1 (Subtype.ext h)) ?_
    rw [Subgroup.mem_centralizer_singleton_iff]
    have := Subgroup.mem_centralizer_singleton_iff.mp (hKv hc)
    exact congrArg Subtype.val this
  have hZnt : ¬ K ≤ centralizer (Z' : Set ↥N) := by
    intro hKZ
    apply hKM
    rintro _ ⟨c, hc, rfl⟩
    have hcZ : (c : G) ∈ centralizer ((Zr r M : Subgroup G) : Set G) := by
      rw [Subgroup.mem_centralizer_iff]
      intro w hw
      have := Subgroup.mem_centralizer_iff.mp (hKZ hc) ⟨w, hZN hw⟩ hw
      exact congrArg Subtype.val this
    rw [← hZM]
    exact Subgroup.centralizer_le_normalizer _ hcZ
  have hP3 : ∀ v ∈ V', v ≠ 1 → ∀ c ∈ K, c ∈ centralizer ({v} : Set ↥N) →
      c ∈ normalizer (Z' : Set ↥N) := by
    intro v hv' hv1 c hc hcv
    have hcM : (c : G) ∈ M := by
      refine hCvM (v : G) hv' (fun h => hv1 (Subtype.ext h)) ?_
      rw [Subgroup.mem_centralizer_singleton_iff]
      exact congrArg Subtype.val (Subgroup.mem_centralizer_singleton_iff.mp hcv)
    have hcZ : (c : G) ∈ normalizer ((Zr r M : Subgroup G) : Set G) := hZM.ge hcM
    rw [Subgroup.mem_normalizer_iff] at hcZ ⊢
    intro w
    exact hcZ (w : G)
  have hGH : GHList (↥K ⧸ center ↥K) := by
    let J : Subgroup G := K.map N.subtype
    have hJtop : J ≠ ⊤ := fun hJ => hNtop (top_le_iff.mp (hJ ▸ Subgroup.map_subtype_le K))
    let e₁ : ↥K ≃* ↥J := K.equivMapOfInjective N.subtype N.subtype_injective
    let f : ↥J →* ↥K ⧸ center ↥K := (QuotientGroup.mk' (center ↥K)).comp e₁.symm.toMonoidHom
    have hf : Function.Surjective f :=
      (QuotientGroup.mk'_surjective _).comp e₁.symm.surjective
    exact Generic.ghList_of_surjection hC.ctx.std.kgh hJtop f hf hKc.1.2.1 hKc.1.2.2
  exact h ↥N K hKc hGH r hr hrodd V' Z' hVe' hVc' hZab hZodd hZcop hcomm hVnorm hZnorm hfaith
    hZnt hP3

end CFSG.GH74.GLS.Stage2.Bender.Thm1
