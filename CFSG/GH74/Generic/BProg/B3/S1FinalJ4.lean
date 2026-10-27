module

public import CFSG.GH74.Generic.BProg.B3.S1FinalJ3
public import CFSG.GH74.Generic.BProg.B3.S1L3Pkg

public section

namespace CFSG.GH74.Generic.BProg.B3

namespace S1FinalJ4

open CFSG CFSG.GH74 CFSG.GH74.GLS CFSG.GH74.GLS.TwoThin CFSG.GH74.GLS.C3.Layer1 CFSG.GH74.Generic
  CFSG.GH74.Generic.BProg CFSG.Blueprint CFSG.GH74.L5U5 Subgroup
open CFSG.GH74.Generic.BProg.B3.S1FinalDefs CFSG.GH74.Generic.BProg.B3.S1FinalJ1
  CFSG.GH74.Generic.BProg.B3.S1FinalJ2 CFSG.GH74.Generic.BProg.B3.S1FinalJ3
open scoped MatrixGroups commutatorElement

variable {G : Type} [Group G] [Finite G] {x : G} {K A : Subgroup G} {a : G} {D J J₁ J₂ : Subgroup G}

theorem exists_d (H : JSetup x K A a D J J₁ J₂) (hL : B1.QShape3SD (J0 a J))
    (hodd : Odd (Nat.card (center ↥(PumpCalc.bar a J)))) {c : G} (hcA : c ∈ A)
    (hcout : rhoA H ⟨c, hcA⟩ ∉ (MulAut.conj : J0 a J →* MulAut (J0 a J)).range) :
    ∃ (d : ↥J) (δ : J0 a J), d * d = 1 ∧ Pi0 H.hJa d = δ ∧ orderOf δ = 2 ∧ δ ≠ beta0 H ∧
      (∀ e ∈ A, e * (d : G) = d * e) := by
  classical
  set γ : MulAut (J0 a J) := rhoA H ⟨c, hcA⟩ with hγ
  have hγ2 : γ * γ = 1 := rhoA_sq H ⟨c, hcA⟩
  have hγβ : γ (beta0 H) = beta0 H := by
    have hcomm : (⟨c, hcA⟩ : ↥A) * ⟨x * a, hxaA H⟩ = ⟨x * a, hxaA H⟩ * ⟨c, hcA⟩ :=
      Subtype.ext (H.hAcomm c hcA (x * a) (hxaA H))
    have h1 : γ * MulAut.conj (beta0 H) = MulAut.conj (beta0 H) * γ := by
      have := congrArg (rhoA H) hcomm
      rw [map_mul, map_mul, rho_xa H] at this
      exact this
    have h2 : MulAut.conj (γ (beta0 H)) = MulAut.conj (beta0 H) := by
      rw [← aut_mul_conj_mul_inv, h1, mul_assoc, mul_inv_cancel, mul_one]
    exact conj_injective H h2
  obtain ⟨δ, hδ2, hδβ, hδc, hγδ⟩ :=
    l3_outer_involution_commuting hL (orderOf_beta0 H) γ hγ2 hγβ hcout
  have hδsq : δ * δ = 1 := by
    have := pow_orderOf_eq_one δ
    rwa [hδ2, pow_two] at this
  have hδ1 : δ ≠ 1 := fun h => by
    rw [h, orderOf_one] at hδ2
    omega
  set E : Subgroup G := closure ({x * a, c} : Set G) with hE
  have hEA : E ≤ A := by
    rw [hE, Subgroup.closure_le]
    intro g hg
    rcases hg with rfl | hg
    · exact hxaA H
    · rw [Set.mem_singleton_iff.1 hg]; exact hcA
  have hEN : E ≤ NJ a J := hEA.trans (A_le_NJ H)
  have hE2 : ∀ e ∈ E, e * e = 1 := fun e he => H.hAsq e (hEA he)
  have hy : ∀ (e : G) (he : e ∈ E), rho H.hJa ⟨e, hEN he⟩ δ = δ := by
    intro e he
    refine Subgroup.closure_induction (p := fun e he => rho H.hJa ⟨e, hEN he⟩ δ = δ) ?_ ?_ ?_ ?_ he
    · intro g hg
      rcases hg with hg | hg
      · subst hg
        have h1 : rho H.hJa ⟨x * a, hEN (Subgroup.subset_closure (Set.mem_insert _ _))⟩ =
            MulAut.conj (beta0 H) := rho_xa H
        rw [h1, MulAut.conj_apply, ← hδc, mul_inv_cancel_right]
      · have hgc : g = c := Set.mem_singleton_iff.1 hg
        subst hgc
        exact hγδ
    · exact by
        have : (⟨1, hEN (E.one_mem)⟩ : ↥(NJ a J)) = 1 := rfl
        rw [this, map_one]; rfl
    · intro g₁ g₂ hg₁ hg₂ h₁ h₂
      have : (⟨g₁ * g₂, hEN (E.mul_mem hg₁ hg₂)⟩ : ↥(NJ a J)) =
          ⟨g₁, hEN hg₁⟩ * ⟨g₂, hEN hg₂⟩ := rfl
      rw [this, map_mul]
      show rho H.hJa ⟨g₁, hEN hg₁⟩ (rho H.hJa ⟨g₂, hEN hg₂⟩ δ) = δ
      rw [h₂, h₁]
    · intro g hg h
      have : (⟨g⁻¹, hEN (E.inv_mem hg)⟩ : ↥(NJ a J)) = (⟨g, hEN hg⟩ : ↥(NJ a J))⁻¹ := rfl
      rw [this, map_inv]
      have h' := congrArg (⇑(rho H.hJa ⟨g, hEN hg⟩)⁻¹) h
      rw [MulAut.inv_apply_self] at h'
      exact h'.symm
  obtain ⟨d, hd2, hd1, hdδ, hdE⟩ :=
    S1FinalLift.exists_lift_invol H.hJa hodd hEN hE2 hδsq hδ1 hy
  refine ⟨d, δ, hd2, hdδ, hδ2, hδβ, ?_⟩
  have hAc := A_eq_closure H hcA hcout
  have hdad : (a : G) * d = d * a := (Subgroup.mem_centralizer_singleton_iff.1 (H.hJa d.2)).symm
  have hle : A ≤ centralizer ({(d : G)} : Set G) := by
    rw [hAc, Subgroup.closure_le]
    intro g hg
    rcases hg with hg | hg
    · rw [hg]
      exact Subgroup.mem_centralizer_singleton_iff.2 hdad
    · rcases hg with hg | hg
      · have hxa : (x * a) * (d : G) = d * (x * a) :=
          hdE (x * a) (Subgroup.subset_closure (Set.mem_insert _ _))
        have hgx : g = (x * a) * a := by rw [hg, mul_assoc, H.hAsq a H.haA, mul_one]
        rw [hgx]
        exact (centralizer ({(d : G)} : Set G)).mul_mem
          (Subgroup.mem_centralizer_singleton_iff.2 hxa)
          (Subgroup.mem_centralizer_singleton_iff.2 hdad)
      · rw [Set.mem_singleton_iff.1 hg]
        exact Subgroup.mem_centralizer_singleton_iff.2
          (hdE c (Subgroup.subset_closure (Set.mem_insert_of_mem _ rfl)))
  intro e he
  exact Subgroup.mem_centralizer_singleton_iff.1 (hle he)

theorem d_not_mem_A (H : JSetup x K A a D J J₁ J₂) {c : G} (hcA : c ∈ A)
    (hcout : rhoA H ⟨c, hcA⟩ ∉ (MulAut.conj : J0 a J →* MulAut (J0 a J)).range) {d : ↥J}
    {δ : J0 a J} (hdδ : Pi0 H.hJa d = δ) (hδ1 : δ ≠ 1) (hδβ : δ ≠ beta0 H) : (d : G) ∉ A := by
  intro hdA
  have h1 : rhoA H ⟨(d : G), hdA⟩ = MulAut.conj δ := by
    rw [← hdδ]
    exact rho_of_mem H.hJa ⟨(d : G), A_le_NJ H hdA⟩ d.2
  have h2 := inner_values H hcA hcout (d : G) hdA (by rw [h1]; exact ⟨δ, rfl⟩)
  rw [h1] at h2
  rcases h2 with h | h
  · exact hδ1 (conj_injective H (by rw [h, map_one]))
  · exact hδβ (conj_injective H h)

abbrev Theta (A : Subgroup G) (d : G) (J₂ : Subgroup G) : Subgroup G :=
  (A ⊔ zpowers d) ⊓ centralizerSection J₂ (pPrimeCoreOf 2 J₂)

theorem card_le_two_of_forall {Y : Type} [Group Y] (K : Subgroup Y) (y : Y)
    (h : ∀ k ∈ K, k = 1 ∨ k = y) : Nat.card ↥K ≤ 2 := by
  have hsub : (K : Set Y) ⊆ {1, y} := fun k hk => by
    rcases h k hk with rfl | rfl <;> simp
  have h1 := Set.ncard_le_ncard hsub (Set.toFinite _)
  have h2 : ({1, y} : Set Y).ncard ≤ 2 := by
    have := Set.ncard_insert_le (1 : Y) ({y} : Set Y)
    rwa [Set.ncard_singleton] at this
  have h3 : Nat.card ↥K = (K : Set Y).ncard := Nat.card_coe_set_eq (K : Set Y)
  omega

theorem card_Theta_le_four (H : JSetup x K A a D J J₁ J₂) (hL : B1.QShape3SD (J0 a J))
    (hodd : Odd (Nat.card (center ↥(PumpCalc.bar a J)))) {c : G} (hcA : c ∈ A)
    (hcout : rhoA H ⟨c, hcA⟩ ∉ (MulAut.conj : J0 a J →* MulAut (J0 a J)).range) {d : ↥J}
    {δ : J0 a J} (hd2 : d * d = 1) (hdδ : Pi0 H.hJa d = δ) (hδ2 : orderOf δ = 2)
    (hδβ : δ ≠ beta0 H) (hdA : ∀ e ∈ A, e * (d : G) = d * e) :
    Nat.card ↥(Theta A (d : G) J₂) ≤ 4 := by
  classical
  obtain ⟨F'', _, _, S, hodd'', hF'', ⟨eS⟩, hβS, hQS, hB4, hker⟩ := exists_identification hL H hodd
  have hδsq : δ * δ = 1 := by
    have := pow_orderOf_eq_one δ
    rwa [hδ2, pow_two] at this
  have hδ1 : δ ≠ 1 := fun h => by
    rw [h, orderOf_one] at hδ2
    omega
  have hdd2 : (d : G) * d = 1 := congrArg Subtype.val hd2
  have hd1 : (d : G) ≠ 1 := fun h => hδ1 (by
    rw [← hdδ]
    have : d = 1 := Subtype.ext h
    rw [this, map_one])
  have hdord : orderOf (d : G) = 2 := orderOf_eq_prime (by rw [pow_two]; exact hdd2) hd1
  have hdN : (d : G) ∈ NJ a J := S1FinalLift.J_le_NJ H.hJa d.2
  have hBN : A ⊔ zpowers (d : G) ≤ NJ a J :=
    sup_le (A_le_NJ H) (Subgroup.zpowers_le.2 hdN)
  have hBdec : ∀ e ∈ A ⊔ zpowers (d : G), e ∈ A ∨ ∃ e₀ ∈ A, e = e₀ * d := by
    intro e he
    obtain ⟨e₀, he₀, b, hb, rfl⟩ := B1.PilotS5.mem_sup_of_commute (A := A) (B := zpowers (d : G))
      (fun u hu b hb => by
        obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.1 hb
        exact ((Commute.zpow_right (show Commute u (d : G) from hdA u hu) k)).eq) he
    rcases B1.PilotS5.mem_zpowers_of_two hdord hb with rfl | rfl
    · left; simpa using he₀
    · right; exact ⟨e₀, he₀, rfl⟩
  have hBsq : ∀ e ∈ A ⊔ zpowers (d : G), e * e = 1 := by
    intro e he
    rcases hBdec e he with h | ⟨e₀, he₀, rfl⟩
    · exact H.hAsq e h
    · have hc : e₀ * (d : G) = d * e₀ := hdA e₀ he₀
      calc e₀ * d * (e₀ * d) = e₀ * (d * e₀) * d := by group
        _ = e₀ * (e₀ * d) * d := by rw [← hc]
        _ = (e₀ * e₀) * (d * d) := by group
        _ = 1 := by rw [H.hAsq e₀ he₀, hdd2, one_mul]
  have hΘN : Theta A (d : G) J₂ ≤ NJ a J := inf_le_left.trans hBN
  let ρΘ : ↥(Theta A (d : G) J₂) →* MulAut (J0 a J) :=
    (rho H.hJa).comp (Subgroup.inclusion hΘN)
  have hkerle : ∀ k ∈ ρΘ.ker.map (Theta A (d : G) J₂).subtype, k = 1 ∨ k = a := by
    rintro _ ⟨e, he, rfl⟩
    have he1 : rho H.hJa ⟨(e : G), hΘN e.2⟩ = 1 := he
    have heB : (e : G) ∈ A ⊔ zpowers (d : G) := e.2.1
    rcases hBdec (e : G) heB with heA | ⟨e₀, he₀, hee⟩
    · have hcs : (e : G) ∈ centralizerSection J (pPrimeCoreOf 2 J) :=
        (rho_eq_one_iff H.hc.obs.comp ⟨(e : G), hΘN e.2⟩).1 he1
      exact H.hc.cA_eq (e : G) heA hcs
    · exfalso
      have hρe : rho H.hJa ⟨(e : G), hΘN e.2⟩ =
          rhoA H ⟨e₀, he₀⟩ * MulAut.conj δ := by
        have h1 : (⟨(e : G), hΘN e.2⟩ : ↥(NJ a J)) =
            (⟨e₀, A_le_NJ H he₀⟩ : ↥(NJ a J)) * ⟨(d : G), hdN⟩ := Subtype.ext hee
        have h2 : rho H.hJa ⟨(d : G), hdN⟩ = MulAut.conj δ := by
          rw [← hdδ]
          exact rho_of_mem H.hJa ⟨(d : G), hdN⟩ d.2
        rw [h1, map_mul, h2]
        rfl
      rw [he1] at hρe
      have hρe0 : rhoA H ⟨e₀, he₀⟩ = (MulAut.conj δ)⁻¹ := eq_inv_of_mul_eq_one_left hρe.symm
      have hinvδ : δ⁻¹ = δ := inv_eq_of_mul_eq_one_right hδsq
      have hρe1 : rhoA H ⟨e₀, he₀⟩ = MulAut.conj δ := by
        rw [hρe0, ← map_inv, hinvδ]
      have hin : rhoA H ⟨e₀, he₀⟩ ∈ (MulAut.conj : J0 a J →* MulAut (J0 a J)).range :=
        ⟨δ, hρe1.symm⟩
      rcases inner_values H hcA hcout e₀ he₀ hin with h | h
      · rw [hρe1] at h
        exact hδ1 (conj_injective H (by rw [h, map_one]))
      · rw [hρe1] at h
        exact hδβ (conj_injective H h)
  have hrangele : ∀ τ ∈ ρΘ.range, τ = 1 ∨ τ = MulAut.conj (beta0 H) := by
    rintro _ ⟨e, rfl⟩
    have heB : (e : G) ∈ A ⊔ zpowers (d : G) := e.2.1
    have heS : (e : G) ∈ centralizerSection J₂ (pPrimeCoreOf 2 J₂) := e.2.2
    have hτ2 : ρΘ e * ρΘ e = 1 := by
      rw [← map_mul]
      have : e * e = 1 := Subtype.ext (hBsq (e : G) heB)
      rw [this, map_one]
    refine hB4 (ρΘ e) hτ2 ?_
    intro s hs
    rw [← hQS] at hs
    obtain ⟨k, rfl⟩ := hs
    have hkJ : (k : G) ∈ J := H.hJ₂ k.2
    show rho H.hJa ⟨(e : G), hΘN e.2⟩ (Pi0 H.hJa ⟨(k : G), hkJ⟩) = Pi0 H.hJa ⟨(k : G), hkJ⟩
    rw [rho_Pi0]
    have hcomm : ⁅(e : G), (k : G)⁆ ∈ pPrimeCoreOf 2 J₂ := by
      have := heS.2.2 (k : G) k.2
      have h' : ⁅(e : G), (k : G)⁆ = (⁅(k : G), (e : G)⁆)⁻¹ := (commutatorElement_inv _ _).symm
      rw [h']
      exact (pPrimeCoreOf 2 J₂).inv_mem this
    obtain ⟨n, hn, hne⟩ := hcomm
    have hn1 : sigma2 H.hJa H.hJ₂ n = 1 := hker n hn
    have hmem : (e : G) * (k : G) * (e : G)⁻¹ ∈ J := mem_normalizer_conj (hΘN e.2).1 ⟨(k : G), hkJ⟩
    have hsplit : (⟨(e : G) * (k : G) * (e : G)⁻¹, hmem⟩ : ↥J) =
        Subgroup.inclusion H.hJ₂ n * ⟨(k : G), hkJ⟩ := by
      apply Subtype.ext
      show (e : G) * (k : G) * (e : G)⁻¹ = (n : G) * (k : G)
      have hne' : (n : G) = ⁅(e : G), (k : G)⁆ := hne
      rw [hne']
      simp only [commutatorElement_def]
      group
    rw [hsplit, map_mul]
    show sigma2 H.hJa H.hJ₂ n * _ = _
    rw [hn1, one_mul]
  have h1 : Nat.card ↥(ρΘ.ker.map (Theta A (d : G) J₂).subtype) ≤ 2 :=
    card_le_two_of_forall _ a hkerle
  have h2 : Nat.card ↥ρΘ.range ≤ 2 := card_le_two_of_forall _ (MulAut.conj (beta0 H)) hrangele
  have hcardker : Nat.card ↥(ρΘ.ker.map (Theta A (d : G) J₂).subtype) = Nat.card ρΘ.ker :=
    Subgroup.card_map_of_injective (Subgroup.subtype_injective _)
  have hcard : Nat.card ↥(Theta A (d : G) J₂) = Nat.card ρΘ.ker * Nat.card ↥ρΘ.range := by
    rw [Subgroup.card_eq_card_quotient_mul_card_subgroup ρΘ.ker, mul_comm]
    congr 1
    exact Nat.card_congr (QuotientGroup.quotientKerEquivRange ρΘ).toEquiv
  rw [hcard]
  calc Nat.card ρΘ.ker * Nat.card ↥ρΘ.range ≤ 2 * 2 := Nat.mul_le_mul (hcardker ▸ h1) h2
    _ = 4 := by norm_num

end S1FinalJ4

end CFSG.GH74.Generic.BProg.B3
