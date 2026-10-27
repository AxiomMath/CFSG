module

public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.Setup.WreathA3Sel
public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.Setup.CampbellNatContract
public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.Setup.WreathA3Sub3
public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.Setup.WreathShortMap

public section

namespace CFSG.QuasithinUnique.Setup.Wreath

open Subgroup CFSG.Open CFSG.QuasithinUnique CFSG.QuasithinUnique.Setup.Campbell
  CFSG.Quasithin.BlueprintB2
open scoped commutatorElement

variable {G : Type*} [Group G] [Finite G]

omit [Finite G] in
theorem iSup_blockQ_eq_commutator {Q N : Subgroup G} {r : ℕ} {L : Fin r → Subgroup G}
    (hN : N = ⨆ i, L i) (hcomm : ∀ i, ⁅Q, L i⁆ = blockQ (L i)) (hUQ : ∀ i, blockQ (L i) ≤ Q) :
    (⨆ i, blockQ (L i) : Subgroup G) = ⁅Q, N⁆ := by
  set U : Subgroup G := ⨆ i, blockQ (L i) with hU
  have hLN : ∀ i, L i ≤ N := fun i => by
    rw [hN]
    exact le_iSup L i
  have hLU : ∀ i, L i ≤ normalizer (U : Set G) := by
    intro i l hl
    have key : ∀ l ∈ L i, ∀ x ∈ U, l * x * l⁻¹ ∈ U := by
      intro l hl x hx
      refine Subgroup.iSup_induction (fun j => blockQ (L j)) (C := fun x => l * x * l⁻¹ ∈ U) hx
        ?_ ?_ ?_
      · intro j u hu
        have h1 : ⁅l, u⁆ ∈ ⁅L i, Q⁆ := Subgroup.commutator_mem_commutator hl (hUQ j hu)
        rw [Subgroup.commutator_comm, hcomm i] at h1
        have h2 : l * u * l⁻¹ = ⁅l, u⁆ * u := by simp [commutatorElement_def]
        rw [h2]
        exact U.mul_mem (Subgroup.mem_iSup_of_mem i h1) (Subgroup.mem_iSup_of_mem j hu)
      · simp
      · intro x y hx hy
        have : l * (x * y) * l⁻¹ = (l * x * l⁻¹) * (l * y * l⁻¹) := by group
        rw [this]
        exact U.mul_mem hx hy
    exact mem_normalizer_of_conj_mem (key l hl)
      (fun x hx => by simpa using key l⁻¹ ((L i).inv_mem hl) x hx)
  apply le_antisymm
  · refine iSup_le fun i => ?_
    rw [← hcomm i]
    exact Subgroup.commutator_mono le_rfl (hLN i)
  · rw [Subgroup.commutator_le]
    intro q hq n hn
    have hn' : n ∈ ⨆ i, L i := by rw [← hN]; exact hn
    refine (Subgroup.iSup_induction L (C := fun n => n ∈ N ∧ ⁅q, n⁆ ∈ U) hn' ?_ ?_ ?_).2
    · intro i l hl
      refine ⟨hLN i hl, ?_⟩
      have h1 : ⁅q, l⁆ ∈ ⁅Q, L i⁆ := Subgroup.commutator_mem_commutator hq hl
      rw [hcomm i] at h1
      exact Subgroup.mem_iSup_of_mem i h1
    · exact ⟨N.one_mem, by simp⟩
    · rintro n n' ⟨hnN, hn1⟩ ⟨hn'N, hn2⟩
      refine ⟨N.mul_mem hnN hn'N, ?_⟩
      have e : ⁅q, n * n'⁆ = ⁅q, n⁆ * (n * ⁅q, n'⁆ * n⁻¹) := by
        simp only [commutatorElement_def]
        group
      rw [e]
      refine U.mul_mem hn1 ?_
      have hnU : n ∈ normalizer (U : Set G) := by
        rw [hN] at hnN
        refine (iSup_le hLU : (⨆ i, L i) ≤ normalizer (U : Set G)) hnN
      exact (Subgroup.mem_normalizer_iff.mp hnU _).mp hn2

omit [Finite G] in
theorem relIndex_sup_right_of_le_normalizer {Q L' : Subgroup G}
    (h : L' ≤ normalizer (Q : Set G)) : Q.relIndex (L' ⊔ Q) = Q.relIndex L' := by
  set M : Subgroup G := L' ⊔ Q with hM
  have hLM : L' ≤ M := le_sup_left
  have hQM : Q ≤ M := le_sup_right
  have hMn : M ≤ normalizer (Q : Set G) := sup_le h Subgroup.le_normalizer
  have : (Q.subgroupOf M).Normal := (Subgroup.normal_subgroupOf_iff_le_normalizer hQM).2 hMn
  have h1 : L'.subgroupOf M ⊔ Q.subgroupOf M = ⊤ := by
    refine top_unique fun x _ => ?_
    obtain ⟨q, hq, l, hl, hql⟩ := CFSG.QuasithinUnique.Setup.Layer.mem_sup_mul h
      (show (x : G) ∈ Q ⊔ L' by rw [sup_comm]; exact x.2)
    have hx : x = ⟨q, hQM hq⟩ * ⟨l, hLM hl⟩ := Subtype.ext hql
    rw [hx]
    exact Subgroup.mul_mem _ (Subgroup.mem_sup_right (Subgroup.mem_subgroupOf.mpr hq))
      (Subgroup.mem_sup_left (Subgroup.mem_subgroupOf.mpr hl))
  have h2 : Q.relIndex M = (Q.subgroupOf M).relIndex (L'.subgroupOf M) := by
    rw [← Subgroup.relIndex_sup_right (H := L'.subgroupOf M) (K := Q.subgroupOf M), h1,
      Subgroup.relIndex_top_right]
    rfl
  rw [h2, Subgroup.relIndex_subgroupOf hLM]

theorem exists_conjEnum (T L : Subgroup G) : ∃ (r : ℕ) (Lf : Fin r → Subgroup G), ConjEnum T L Lf := by
  classical
  let S : Set (Subgroup G) := {K | ∃ t ∈ T, K = L.map (MulAut.conj t).toMonoidHom}
  have hfin : S.Finite := Set.toFinite S
  let e := hfin.toFinset.equivFin
  refine ⟨hfin.toFinset.card, fun i => ((e.symm i : ↥hfin.toFinset) : Subgroup G), ?_, ?_, ?_⟩
  · intro i j hij
    exact e.symm.injective (Subtype.ext hij)
  · intro i
    have := (e.symm i).2
    rw [Set.Finite.mem_toFinset] at this
    exact this
  · intro t ht
    have hmem : L.map (MulAut.conj t).toMonoidHom ∈ hfin.toFinset := by
      rw [Set.Finite.mem_toFinset]
      exact ⟨t, ht, rfl⟩
    exact ⟨e ⟨_, hmem⟩, by simp⟩

namespace A3SelHyp

variable {X T N R P : Subgroup G} (h : A3SelHyp X T N R P)

include h

theorem L_facts {V : Subgroup G} (hV : CFSG.Quasithin.IsTwoReducedIn P V)
    (ρ : ↥P →* Matrix.SpecialLinearGroup (Fin 2) (ZMod 2)) (hρ : Function.Surjective ρ)
    (ψ : ↥V →* Multiplicative (Fin 2 → ZMod 2)) (hψ : Function.Surjective ψ)
    (hψρ : ∀ (p : ↥P) (v v' : ↥V), (v' : G) = (p : G) * (v : G) * (p : G)⁻¹ →
      Multiplicative.toAdd (ψ v') =
        (ρ p : Matrix (Fin 2) (Fin 2) (ZMod 2)).mulVec (Multiplicative.toAdd (ψ v)))
    (hψker : ψ.ker = (Subgroup.centralizer (oddOrderSubgroup P : Set G)).subgroupOf V)
    (hJV : ⁅CFSG.Quasithin.thompsonJ R, V⁆ ≠ ⊥) :
    P = oddOrderSubgroup P ⊔ R ∧ IsShort2 (oddOrderSubgroup P) ∧
      Nat.card (↥(oddOrderSubgroup P) ⧸ CFSG.pCore 2 ↥(oddOrderSubgroup P)) = 3 ∧
      ⁅oddOrderSubgroup P, CFSG.Quasithin.thompsonJ R⁆ = oddOrderSubgroup P := by
  classical
  obtain ⟨K, ρ', φ, hset⟩ := h.natQuotSetting hV ρ hρ ψ hψ hψρ hψker
  have hRP := h.R_le_P
  have hVP : V ≤ P := hV.1
  have hJ : ⁅elemThompsonIn 2 (R.subgroupOf P), V.subgroupOf P⁆ ≠ ⊥ := by
    intro hb
    apply hJV
    have h1 := congrArg (Subgroup.map P.subtype) hb
    rwa [Subgroup.map_commutator, elemThompsonIn_subgroupOf_map_eq hRP,
      Subgroup.map_subgroupOf_eq_of_le hVP, Subgroup.map_bot] at h1
  obtain ⟨hsup, hchi, hcomm, -, hA4⟩ :=
    hset.actual_Campbell_natural_minimal_parabolic_chi0_block h.charTwo_top h.noCharNormal_top hJ
      (n := 1) le_rfl (by simp)
  obtain ⟨hAlt, -⟩ := hA4 rfl
  set L' : Subgroup ↥P := oddOrderSubgroup (⊤ : Subgroup ↥P) with hL'
  have hLmap : L'.map P.subtype = oddOrderSubgroup P := oddOrderSubgroup_top_map P
  have hshort' : IsShort2 L' := hchi.1.1
  have hshort : IsShort2 (oddOrderSubgroup P) := by
    rw [← hLmap]
    exact IsShort2.map_of_injective P.subtype P.subtype_injective hshort'
  have hcard' : Nat.card (↥L' ⧸ CFSG.pCore 2 ↥L') = 3 := by
    obtain ⟨α, hα, hker, -⟩ := hAlt
    have e : (↥L' ⧸ CFSG.pCore 2 ↥L') ≃* ↥(alternatingGroup (Fin 3)) :=
      (QuotientGroup.quotientMulEquivOfEq hker.symm).trans
        (QuotientGroup.quotientKerEquivOfSurjective α hα)
    rw [Nat.card_congr e.toEquiv, Nat.card_eq_fintype_card, card_alternatingGroup]
    simp [Nat.factorial]
  have hcard : Nat.card (↥(oddOrderSubgroup P) ⧸ CFSG.pCore 2 ↥(oddOrderSubgroup P)) = 3 := by
    rw [← hLmap]
    rw [card_quot_pCore_map_injective P.subtype P.subtype_injective L']
    exact hcard'
  refine ⟨?_, hshort, hcard, ?_⟩
  · have h1 := congrArg (Subgroup.map P.subtype) hsup
    rw [Subgroup.map_sup, hLmap, Subgroup.map_subgroupOf_eq_of_le hRP, Subgroup.map_top,
      Subgroup.range_subtype] at h1
    exact h1.symm
  · have h1 := congrArg (Subgroup.map P.subtype) hcomm
    rwa [Subgroup.map_commutator, hLmap, elemThompsonIn_subgroupOf_map_eq hRP] at h1

omit [Finite G] in
theorem a3SubHyp_of_facts
    (hfacts : P = oddOrderSubgroup P ⊔ R ∧ IsShort2 (oddOrderSubgroup P) ∧
      Nat.card (↥(oddOrderSubgroup P) ⧸ CFSG.pCore 2 ↥(oddOrderSubgroup P)) = 3 ∧
      ⁅oddOrderSubgroup P, CFSG.Quasithin.thompsonJ R⁆ = oddOrderSubgroup P) :
    A3SubHyp X T N R P (oddOrderSubgroup P) :=
  { T_sylow := h.T_sylow, N_le := h.N_le, N_norm := h.N_norm, X_eq := h.X_eq,
    N_noTwo := h.N_noTwo, R_le_T := h.R_le_T, T_norm_R := h.T_norm_R, R_sylow := h.R_sylow,
    charTwo := h.charTwo, R_le_P := h.R_le_P, P_le := h.P_le, X_eq_P := h.X_eq_P,
    L_le := oddOrderSubgroup_le P,
    L_norm := Subgroup.le_normalizer.trans (normalizer_le_normalizer_oddOrderSubgroup P),
    short := hfacts.2.1, ord3 := hfacts.2.2.1, P_eq := hfacts.1,
    L_J := hfacts.2.2.2 }

end A3SelHyp


namespace A3SubHyp

variable {X T N R P L : Subgroup G} (h : A3SubHyp X T N R P L)

include h

omit [Finite G] in
theorem NR_le_X : N ⊔ R ≤ X := sup_le h.N_le h.R_le_X

theorem centralizer_NR_U :
    (N ⊔ R) ⊓ Subgroup.centralizer ((⁅blockQ (N ⊔ R), N⁆ : Subgroup G) : Set G) =
      blockQ (N ⊔ R) := by
  classical
  obtain ⟨-, -, -, hXU, hUZ, -⟩ := h.block_centrality
  set Q : Subgroup G := blockQ (N ⊔ R) with hQ
  set U : Subgroup G := ⁅Q, N⁆ with hU
  have hUQ : U ≤ Q := hUZ.trans (centerTorsion_le 2 Q)
  have hQU : Q ≤ normalizer (U : Set G) := fun q hq =>
    hXU (h.R_le_X (h.Q_le_R hq))
  have hodd : ∀ c ∈ N ⊔ R, (∀ u ∈ U, c * u = u * c) → Odd (orderOf c) → c = 1 := by
    intro c hc hcU hodd
    have hNn : N ⊔ R ≤ normalizer (N : Set G) :=
      sup_le Subgroup.le_normalizer (fun r hr => h.N_norm (h.R_le_X hr))
    have hcN : c ∈ N := mem_of_odd_of_sup_eq (Y := N ⊔ R) (J := N) (T := R) hNn le_sup_right
      h.R_sylow.2.1 rfl hc hodd
    have hdisp : ∀ x ∈ Q, x⁻¹ * (c * x * c⁻¹) ∈ U := by
      intro x hx
      have h1 : ⁅x⁻¹, c⁆ ∈ ⁅Q, N⁆ := Subgroup.commutator_mem_commutator (Q.inv_mem hx) hcN
      have e : x⁻¹ * (c * x * c⁻¹) = ⁅x⁻¹, c⁆ := by rw [commutatorElement_def]; group
      rw [e]
      exact h1
    have hcent := centralizes_of_odd_trivial_factors Q_two hUQ hQU (NR_norm_Q hc) hodd hcU
      hdisp
    have hcQ : c ∈ Q :=
      h.charTwo ⟨hc, Subgroup.mem_centralizer_iff.mpr fun x hx => (hcent x hx).symm⟩
    obtain ⟨k, hk⟩ := Q_two ⟨c, hcQ⟩
    have hk' : c ^ 2 ^ k = 1 := by simpa using congrArg Subtype.val hk
    have hdvd : orderOf c ∣ 2 ^ k := orderOf_dvd_of_pow_eq_one hk'
    have hcop : Nat.Coprime (orderOf c) (2 ^ k) :=
      Nat.Coprime.pow_right k (Nat.coprime_two_right.2 hodd)
    exact orderOf_eq_one_iff.1 (Nat.Coprime.eq_one_of_dvd hcop hdvd)
  have h2el : ∀ c ∈ (N ⊔ R) ⊓ Subgroup.centralizer (U : Set G), ∃ a : ℕ, c ^ 2 ^ a = 1 := by
    rintro c ⟨hc, hcU⟩
    obtain ⟨a, b, hb, hab⟩ := Nat.exists_eq_two_pow_mul_odd (orderOf_pos c).ne'
    have hcU' : ∀ u ∈ U, c * u = u * c := fun u hu =>
      (Subgroup.mem_centralizer_iff.mp hcU u hu).symm
    have hd : c ^ 2 ^ a ∈ N ⊔ R := (N ⊔ R).pow_mem hc _
    have hdU : ∀ u ∈ U, c ^ 2 ^ a * u = u * c ^ 2 ^ a := fun u hu =>
      ((show Commute c u from hcU' u hu).pow_left (2 ^ a))
    have hdord : orderOf (c ^ 2 ^ a) = b := by
      have hdvd : 2 ^ a ∣ orderOf c := ⟨b, hab⟩
      rw [orderOf_pow_of_dvd (pow_ne_zero _ two_ne_zero) hdvd, hab]
      exact Nat.mul_div_cancel_left b (pow_pos two_pos a)
    have h1 : c ^ 2 ^ a = 1 := hodd _ hd hdU (by rw [hdord]; exact hb)
    exact ⟨a, h1⟩
  have hW2 : IsPGroup 2 ↥((N ⊔ R) ⊓ Subgroup.centralizer (U : Set G)) := by
    rintro ⟨c, hc⟩
    obtain ⟨a, ha⟩ := h2el c hc
    exact ⟨a, Subtype.ext (by simpa using ha)⟩
  have hWn : N ⊔ R ≤ normalizer (((N ⊔ R) ⊓ Subgroup.centralizer (U : Set G) : Subgroup G) :
      Set G) := by
    intro g hg
    have hgU : g ∈ normalizer (U : Set G) := hXU (h.NR_le_X hg)
    have key : ∀ g ∈ N ⊔ R, ∀ w ∈ (N ⊔ R) ⊓ Subgroup.centralizer (U : Set G),
        g * w * g⁻¹ ∈ (N ⊔ R) ⊓ Subgroup.centralizer (U : Set G) := by
      intro g hg w hw
      obtain ⟨hwNR, hwU⟩ := hw
      have hgU : g ∈ normalizer (U : Set G) := hXU (h.NR_le_X hg)
      refine ⟨(N ⊔ R).mul_mem ((N ⊔ R).mul_mem hg hwNR) ((N ⊔ R).inv_mem hg),
        Subgroup.mem_centralizer_iff.mpr fun u hu => ?_⟩
      have hu' : g⁻¹ * u * g ∈ U := by
        have := (Subgroup.mem_normalizer_iff.mp (Subgroup.inv_mem _ hgU) u).mp hu
        simpa using this
      have hc := Subgroup.mem_centralizer_iff.mp hwU _ hu'
      calc u * (g * w * g⁻¹) = g * ((g⁻¹ * u * g) * w) * g⁻¹ := by group
        _ = g * (w * (g⁻¹ * u * g)) * g⁻¹ := by rw [hc]
        _ = (g * w * g⁻¹) * u := by group
    exact mem_normalizer_of_conj_mem (key g hg) (fun w hw => by simpa using key g⁻¹ ((N ⊔ R).inv_mem hg) w hw)
  apply le_antisymm
  · exact le_pCoreOf_of_normalizes inf_le_left hWn hW2
  · refine le_inf (C1.blockQ_le _) (fun q hq => Subgroup.mem_centralizer_iff.mpr fun u hu => ?_)
    exact ((mem_centerTorsion_iff.mp (hUZ hu)).2.1 q hq).symm

theorem Q_inf_conj {t : G} (ht : t ∈ T) :
    blockQ (N ⊔ R) ⊓ L.map (MulAut.conj t).toMonoidHom = blockQ (L.map (MulAut.conj t).toMonoidHom) := by
  have hLt : L.map (MulAut.conj t).toMonoidHom ≤ N ⊔ R := (Subgroup.map_mono h.L_le).trans (h.conj_P_le ht)
  apply le_antisymm
  · have hnormal : ((blockQ (N ⊔ R) ⊓ L.map (MulAut.conj t).toMonoidHom).subgroupOf
        (L.map (MulAut.conj t).toMonoidHom)).Normal := by
      rw [Subgroup.normal_subgroupOf_iff inf_le_right]
      intro y l hy hl
      refine ⟨?_, ?_⟩
      · exact (Subgroup.mem_normalizer_iff.mp (NR_norm_Q (hLt hl)) y).mp hy.1
      · exact (L.map (MulAut.conj t).toMonoidHom).mul_mem
          ((L.map (MulAut.conj t).toMonoidHom).mul_mem hl hy.2)
          ((L.map (MulAut.conj t).toMonoidHom).inv_mem hl)
    exact CFSG.RankThreeEvenClassification.Helpers.normal_pSubgroup_le_pCoreOf 2 _ _ inf_le_right
      hnormal (Q_two.to_le inf_le_left)
  · exact le_inf ((h.conj_facts ht).2.1.trans (centerTorsion_le 2 _)) (C1.blockQ_le _)

omit [Finite G] in
theorem relIndex_blockQ_conj (t : G) :
    (blockQ (L.map (MulAut.conj t).toMonoidHom)).relIndex (L.map (MulAut.conj t).toMonoidHom) = 3 := by
  have h3 := h.conj_ord3 t
  show ((blockQ (L.map (MulAut.conj t).toMonoidHom)).subgroupOf
    (L.map (MulAut.conj t).toMonoidHom)).index = 3
  have : (blockQ (L.map (MulAut.conj t).toMonoidHom)).subgroupOf (L.map (MulAut.conj t).toMonoidHom) =
      CFSG.pCore 2 ↥(L.map (MulAut.conj t).toMonoidHom) := by
    rw [blockQ_eq_map]
    exact Subgroup.comap_map_eq_self_of_injective (Subgroup.subtype_injective _) _
  rw [this, Subgroup.index_eq_card, h3]

theorem relIndex_Q_conj {t : G} (ht : t ∈ T) :
    (blockQ (N ⊔ R)).relIndex (L.map (MulAut.conj t).toMonoidHom ⊔ blockQ (N ⊔ R)) = 3 := by
  rw [relIndex_sup_right_of_le_normalizer
    (fun x hx => NR_norm_Q (h.conj_P_le ht ((Subgroup.map_mono h.L_le) hx))),
    ← Subgroup.inf_relIndex_right, h.Q_inf_conj ht]
  exact h.relIndex_blockQ_conj t

end A3SubHyp

theorem selected_natural_A3_parabolic_faithful_module {X T N R P V : Subgroup G}
    (h : A3SelHyp X T N R P) (hV : CFSG.Quasithin.IsTwoReducedIn P V)
    (ρ : ↥P →* Matrix.SpecialLinearGroup (Fin 2) (ZMod 2)) (hρ : Function.Surjective ρ)
    (ψ : ↥V →* Multiplicative (Fin 2 → ZMod 2)) (hψ : Function.Surjective ψ)
    (hψρ : ∀ (p : ↥P) (v v' : ↥V), (v' : G) = (p : G) * (v : G) * (p : G)⁻¹ →
      Multiplicative.toAdd (ψ v') =
        (ρ p : Matrix (Fin 2) (Fin 2) (ZMod 2)).mulVec (Multiplicative.toAdd (ψ v)))
    (hψker : ψ.ker = (Subgroup.centralizer (oddOrderSubgroup P : Set G)).subgroupOf V)
    (hJV : ⁅CFSG.Quasithin.thompsonJ R, V⁆ ≠ ⊥)
    {r : ℕ} {Lf : Fin r → Subgroup G} (E : ConjEnum T (oddOrderSubgroup P) Lf) :
    (P = oddOrderSubgroup P ⊔ R ∧ Nonempty (↥(oddOrderSubgroup P) ≃* alternatingGroup (Fin 4)) ∧
      IsChi0Block P (oddOrderSubgroup P) ∧
      ⁅oddOrderSubgroup P, CFSG.Quasithin.thompsonJ R⁆ = oddOrderSubgroup P) ∧
    N = ⨆ i, Lf i ∧
    (∀ i, R ≤ normalizer ((Lf i : Subgroup G) : Set G) ∧
      blockQ (N ⊔ R) ≤ normalizer ((Lf i : Subgroup G) : Set G)) ∧
    (∀ i, ⁅Lf i, CFSG.Quasithin.thompsonJ R⁆ = Lf i) ∧
    (∀ i, ⁅blockQ (N ⊔ R), Lf i⁆ = blockQ (Lf i) ∧
      blockQ (Lf i) ≤ centerTorsion 2 (blockQ (N ⊔ R))) ∧
    ((⨆ i, blockQ (Lf i) : Subgroup G) = ⁅blockQ (N ⊔ R), N⁆ ∧ ⁅blockQ (N ⊔ R), N⁆ ≠ ⊥ ∧
      IsElemAbelian 2 (⁅blockQ (N ⊔ R), N⁆ : Subgroup G) ∧
      X ≤ normalizer ((⁅blockQ (N ⊔ R), N⁆ : Subgroup G) : Set G)) ∧
    (N ⊔ R) ⊓ Subgroup.centralizer ((⁅blockQ (N ⊔ R), N⁆ : Subgroup G) : Set G) =
      blockQ (N ⊔ R) ∧
    (∀ i, (blockQ (N ⊔ R)).relIndex (Lf i ⊔ blockQ (N ⊔ R)) = 3 ∧
      ⁅(⁅blockQ (N ⊔ R), N⁆ : Subgroup G), Lf i⁆ = blockQ (Lf i)) := by
  classical
  obtain ⟨hPL, hshort, hcard, hLJ⟩ :=
    h.L_facts hV ρ hρ ψ hψ hψρ hψker hJV
  have h3 := h.a3SubHyp_of_facts ⟨hPL, hshort, hcard, hLJ⟩
  obtain ⟨-, -, -, hA4, hAlt⟩ := short_order_three_is_alternating_four hshort hcard
  have hN_eq : N = ⨆ i, Lf i := by
    rw [← E.iSup_eq]
    exact (h3.block_centrality).1
  have hLfN : ∀ i, Lf i ≤ N := fun i => by
    rw [hN_eq]
    exact le_iSup Lf i
  have hconj : ∀ i, ∃ t ∈ T, Lf i = (oddOrderSubgroup P).map (MulAut.conj t).toMonoidHom :=
    E.mem
  have hcomm : ∀ i, ⁅blockQ (N ⊔ R), Lf i⁆ = blockQ (Lf i) := fun i => by
    obtain ⟨t, ht, hi⟩ := hconj i
    rw [hi]
    exact (h3.conj_facts ht).1
  have hUZ : ∀ i, blockQ (Lf i) ≤ centerTorsion 2 (blockQ (N ⊔ R)) := fun i => by
    obtain ⟨t, ht, hi⟩ := hconj i
    rw [hi]
    exact (h3.conj_facts ht).2.1
  have hUQ : ∀ i, blockQ (Lf i) ≤ blockQ (N ⊔ R) := fun i => (hUZ i).trans (centerTorsion_le 2 _)
  have hU := iSup_blockQ_eq_commutator hN_eq hcomm hUQ
  refine ⟨⟨hPL, hA4, ⟨h3.block_P, Or.inr (Or.inl hAlt)⟩, hLJ⟩, hN_eq, ?_, ?_, ?_,
    ⟨hU, (h3.block_centrality).2.1, (h3.block_centrality).2.2.1, (h3.block_centrality).2.2.2.1⟩,
    h3.centralizer_NR_U, ?_⟩
  · intro i
    obtain ⟨t, ht, hi⟩ := hconj i
    rw [hi]
    exact ⟨fun x hx => h3.conj_P_le_normalizer (t := t) (h3.R_le_conj_P ht hx),
      (h3.conj_facts ht).2.2⟩
  · intro i
    obtain ⟨t, ht, hi⟩ := hconj i
    rw [hi]
    exact h3.conj_L_J ht
  · exact fun i => ⟨hcomm i, hUZ i⟩
  · intro i
    obtain ⟨t, ht, hi⟩ := hconj i
    refine ⟨?_, ?_⟩
    · rw [hi]
      exact h3.relIndex_Q_conj ht
    · have hb := (short_order_three_is_alternating_four (h3.conj_short t) (h3.conj_ord3 t)).1
      apply le_antisymm
      · rw [← hcomm i]
        exact Subgroup.commutator_mono
          ((h3.block_centrality).2.2.2.2.1.trans (centerTorsion_le 2 _)) le_rfl
      · have hUi : blockQ (Lf i) ≤ ⁅blockQ (N ⊔ R), N⁆ := by
          rw [← hU]
          exact le_iSup (fun j => blockQ (Lf j)) i
        calc blockQ (Lf i) = ⁅blockQ (Lf i), Lf i⁆ := by
              rw [hi]
              exact hb
          _ ≤ ⁅(⁅blockQ (N ⊔ R), N⁆ : Subgroup G), Lf i⁆ :=
              Subgroup.commutator_mono hUi le_rfl

end CFSG.QuasithinUnique.Setup.Wreath
