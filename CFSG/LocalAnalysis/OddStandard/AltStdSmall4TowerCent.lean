module

public import CFSG.LocalAnalysis.OddStandard.AltStdSmall4TowerHyp
public import CFSG.LocalAnalysis.OddStandard.AltStdSmall4FusMainSetup
public import CFSG.LocalAnalysis.OddStandard.AltStdSmall4FusFin
public import CFSG.LocalAnalysis.OddStandard.AltStdEvenFusFin

public section

namespace CFSG.OddStandard.AltStdSmall4.Tower

open Subgroup Equiv Fus Fus.Main Fus.FinCode Fus.FinData

section Count

variable {X Y : Type*} [Group X] [Group Y]

theorem PInv.of_mulEquiv {S : Subgroup X} {S' : Subgroup Y} (e : S ≃* S') (h : PInv S) :
    PInv S' := by
  refine ⟨(Nat.card_congr e.toEquiv).symm.trans h.1, Eq.trans ?_ h.2⟩
  refine (Nat.card_congr (e.toEquiv.subtypeEquiv fun x => ?_)).symm
  simp only [MulEquiv.toEquiv_eq_coe, MulEquiv.coe_toEquiv, ne_eq]
  rw [← map_pow, MulEquiv.map_eq_one_iff, MulEquiv.map_eq_one_iff]

theorem card_sq_eq_one_congr (e : X ≃* Y) :
    Nat.card {x : X // x ^ 2 = 1} = Nat.card {y : Y // y ^ 2 = 1} :=
  Nat.card_congr (e.toEquiv.subtypeEquiv fun x => by
    simp only [MulEquiv.toEquiv_eq_coe, MulEquiv.coe_toEquiv]
    rw [← map_pow, MulEquiv.map_eq_one_iff])

theorem card_sq_eq_one_eq_succ [Finite X] :
    Nat.card {x : X // x ^ 2 = 1} = Nat.card {x : X // x ^ 2 = 1 ∧ x ≠ 1} + 1 := by
  classical
  have := Fintype.ofFinite X
  have h1 : (1 : X) ∈ Finset.univ.filter fun x : X => x ^ 2 = 1 := by simp
  rw [Nat.card_eq_fintype_card, Nat.card_eq_fintype_card, Fintype.card_subtype,
    Fintype.card_subtype, ← Finset.filter_filter, Finset.filter_ne', Finset.card_erase_of_mem h1]
  have := Finset.card_pos.2 ⟨1, h1⟩
  omega

theorem card_sq_eq_one_of_sup {R S : Subgroup X} {z : X} (hRS : R ≤ S) (hzS : z ∈ S)
    (hz : z * z = 1) (hzR : z ∉ R) (hcomm : ∀ r ∈ R, r * z = z * r)
    (hmem : ∀ x ∈ S, x ∈ R ∨ x * z ∈ R) :
    Nat.card {x : S // x ^ 2 = 1} = Nat.card {r : R // r ^ 2 = 1} * 2 := by
  have hsq : ∀ r ∈ R, (r * z) ^ 2 = r ^ 2 := by
    intro r hr
    rw [sq, sq, show r * z * (r * z) = r * (z * r) * z by group, ← hcomm r hr,
      show r * (r * z) * z = r * r * (z * z) by group, hz, mul_one]
  have hval : ∀ x : S, x ^ 2 = 1 ↔ (x : X) ^ 2 = 1 := fun x =>
    ⟨fun h => by simpa using congrArg Subtype.val h, fun h => Subtype.ext (by simpa using h)⟩
  have hvalR : ∀ x : R, x ^ 2 = 1 ↔ (x : X) ^ 2 = 1 := fun x =>
    ⟨fun h => by simpa using congrArg Subtype.val h, fun h => Subtype.ext (by simpa using h)⟩
  let f : {r : R // r ^ 2 = 1} × Bool → {x : S // x ^ 2 = 1} := fun p =>
    cond p.2
      ⟨⟨(p.1.1 : X) * z, mul_mem (hRS p.1.1.2) hzS⟩,
        (hval _).2 ((hsq _ p.1.1.2).trans ((hvalR _).1 p.1.2))⟩
      ⟨⟨p.1.1, hRS p.1.1.2⟩, (hval _).2 ((hvalR _).1 p.1.2)⟩
  have hf : Function.Bijective f := by
    constructor
    · rintro ⟨a, ε⟩ ⟨b, δ⟩ h
      have h' := congrArg (fun x : {x : S // x ^ 2 = 1} => ((x : S) : X)) h
      cases ε <;> cases δ <;> simp only [f, cond_true, cond_false] at h'
      · exact Prod.ext (Subtype.ext (Subtype.ext h')) rfl
      · exfalso
        apply hzR
        have : z = (b.1 : X)⁻¹ * a.1 := by rw [h']; group
        rw [this]
        exact mul_mem (inv_mem b.1.2) a.1.2
      · exfalso
        apply hzR
        have : z = (a.1 : X)⁻¹ * b.1 := by rw [← h']; group
        rw [this]
        exact mul_mem (inv_mem a.1.2) b.1.2
      · exact Prod.ext (Subtype.ext (Subtype.ext (mul_right_cancel h'))) rfl
    · rintro ⟨x, hx⟩
      rcases hmem x x.2 with h | h
      · refine ⟨(⟨⟨x, h⟩, (hvalR _).2 ((hval _).1 hx)⟩, false), ?_⟩
        rfl
      · have hx2 : ((⟨(x : X) * z, h⟩ : R) : X) ^ 2 = 1 := by
          have hxz : (x : X) * z * z = x := by rw [mul_assoc, hz, mul_one]
          have := hsq _ h
          rw [hxz] at this
          exact this.symm ▸ (hval _).1 hx
        refine ⟨(⟨⟨(x : X) * z, h⟩, (hvalR _).2 hx2⟩, true), ?_⟩
        apply Subtype.ext
        apply Subtype.ext
        show (x : X) * z * z = x
        rw [mul_assoc, hz, mul_one]
  rw [← Nat.card_eq_of_bijective f hf, Nat.card_prod, Nat.card_eq_fintype_card (α := Bool),
    Fintype.card_bool]

end Count

section Codes

variable {m : ℕ}

theorem card_sq_eq_one_of_codes (hm : m ≤ 16) {R : Subgroup (Perm (Fin m))} {codes : List ℕ}
    {e : ℕ} (he : enc (1 : Perm (Fin m)) = e) (hR : ∀ σ, σ ∈ R ↔ enc σ ∈ codes)
    (hnd : codes.Nodup) (hcard : Nat.card R = codes.length) :
    Nat.card {σ : R // σ ^ 2 = 1} = (codes.filter fun c => cmul m c c == e).length := by
  classical
  let f : R → codes.toFinset := fun σ =>
    ⟨enc (σ : Perm (Fin m)), List.mem_toFinset.2 ((hR σ).1 σ.2)⟩
  have hf : Function.Bijective f := by
    refine Function.Injective.bijective_of_nat_card_le (fun a b h => ?_) ?_
    · exact Subtype.ext (enc_injective hm (congrArg Subtype.val h))
    · rw [hcard, Nat.card_eq_fintype_card, Fintype.card_coe, List.toFinset_card_of_nodup hnd]
  have hsq : ∀ σ : R, σ ^ 2 = 1 ↔ cmul m (f σ : ℕ) (f σ : ℕ) = e := fun σ => by
    show _ ↔ cmul m (enc (σ : Perm (Fin m))) (enc (σ : Perm (Fin m))) = e
    rw [← he, ← mul_eq_iff hm, ← sq]
    exact ⟨fun h => by simpa using congrArg Subtype.val h, fun h => Subtype.ext (by simpa using h)⟩
  rw [Nat.card_congr ((Equiv.ofBijective f hf).subtypeEquiv
      (q := fun c : codes.toFinset => cmul m (c : ℕ) (c : ℕ) = e) hsq),
    Nat.card_eq_fintype_card, Fintype.card_subtype]
  have hfil : (Finset.univ.filter fun c : codes.toFinset => cmul m (c : ℕ) (c : ℕ) = e).card =
      ((codes.filter fun c => cmul m c c == e).toFinset).card := by
    rw [← Finset.card_map (Function.Embedding.subtype _)]
    congr 1
    ext c
    simp only [Finset.mem_map, Finset.mem_filter, Finset.mem_univ, true_and,
      Function.Embedding.coe_subtype, List.mem_toFinset, List.mem_filter, beq_iff_eq]
    constructor
    · rintro ⟨d, hd, rfl⟩
      exact ⟨List.mem_toFinset.1 d.2, hd⟩
    · rintro ⟨hc, hce⟩
      exact ⟨⟨c, List.mem_toFinset.2 hc⟩, hce, rfl⟩
  rw [hfil, List.toFinset_card_of_nodup (hnd.filter _)]

private theorem e11_eq : enc (1 : Perm (Fin 11)) = e11 := by decide +kernel

private theorem e9_eq : enc (1 : Perm (Fin 9)) = e9 := by decide +kernel

private theorem e8_eq : enc (1 : Perm (Fin 8)) = e8 := by decide +kernel

private theorem e10_eq : enc (1 : Perm (Fin 10)) = e10 := by decide +kernel

theorem card_sq_rBar11 : Nat.card {σ : rBar11 // σ ^ 2 = 1} = 44 := by
  rw [card_sq_eq_one_of_codes (by norm_num) e11_eq mem_rBar11_iff
    (nodup_of_nodupB (by decide +kernel)) (fusR11.card.trans (by decide +kernel))]
  decide +kernel

theorem card_sq_rBarS9 : Nat.card {σ : rBarS9 // σ ^ 2 = 1} = 44 := by
  rw [card_sq_eq_one_of_codes (by norm_num) e9_eq mem_rBarS9_iff
    (nodup_of_nodupB (by decide +kernel)) (fusRS9.card.trans (by decide +kernel))]
  decide +kernel

theorem card_sq_rBarS8 : Nat.card {σ : rBarS8 // σ ^ 2 = 1} = 44 := by
  rw [card_sq_eq_one_of_codes (by norm_num) e8_eq mem_rBarS8_iff
    (nodup_of_nodupB (by decide +kernel)) (fusRS8.card.trans (by decide +kernel))]
  decide +kernel

theorem card_sq_rBar10 : Nat.card {σ : rBar10 // σ ^ 2 = 1} = 44 := by
  rw [card_sq_eq_one_of_codes (by norm_num) e10_eq mem_rBar10_iff
    (nodup_of_nodupB (by decide +kernel)) (fusR10.card.trans (by decide +kernel))]
  decide +kernel

end Codes

section Sylow

variable {G : Type} [Group G] [Finite G] {L Q : Subgroup G} {n : ℕ}
  {θ : L ≃* alternatingGroup (Fin n)} {z : G} {c : Config G L Q n θ z} {H : Subgroup G}
  {Nbar Rbar : Subgroup (Perm (Fin n))}

theorem exists_rStar_equiv (hH : IsHStar c H Nbar) (hle : Rbar ≤ Nbar) :
    Nonempty (rStar c H Rbar ≃* Rbar) := by
  let ψ : rStar c H Rbar →* Perm (Fin n) := (rhoC c).comp (inclusion rStar_le_cent)
  have hinj : Function.Injective ψ := fun a b h => by
    have h' := hH.eq_of_rhoC_eq (rStar_le_H a.2) (rStar_le_H b.2) h
    exact Subtype.ext (show (a : G) = b from
      congrArg (fun x : centralizer ({z} : Set G) => (x : G)) h')
  have hrange : ψ.range = Rbar := by
    apply le_antisymm
    · rintro _ ⟨r, rfl⟩
      exact rhoC_mem_of_mem_rStar (s := inclusion rStar_le_cent r) r.2
    · intro σ hσ
      obtain ⟨h, hhH, hρ⟩ := hH.surj σ (hle hσ)
      have hhR : (h : G) ∈ rStar c H Rbar := mem_rStar_iff'.2 ⟨hhH, hρ ▸ hσ⟩
      exact ⟨⟨h, hhR⟩, hρ⟩
  exact ⟨(MonoidHom.ofInjective hinj).trans (MulEquiv.subgroupCongr hrange)⟩

theorem pinv_sSyl {cc : Subgroup (Perm (Fin n)) → Prop} (hH : IsHStar c H Nbar)
    (hR : FusR n c.hn8 Nbar Rbar 7 cc) (h44 : Nat.card {σ : Rbar // σ ^ 2 = 1} = 44) :
    PInv (sSyl c H Rbar) := by
  refine ⟨hH.card_sSyl_eq hR, ?_⟩
  obtain ⟨e⟩ := exists_rStar_equiv hH hR.le
  have h1 := card_sq_eq_one_of_sup (S := sSyl c H Rbar) rStar_le_sSyl z_mem_sSyl (z_mul_self c)
    hH.z_not_mem_rStar (fun r hr => mem_centralizer_singleton_iff.1 (rStar_le_cent hr))
    (fun x hx => mem_sSyl_iff.1 hx)
  rw [card_sq_eq_one_congr e, h44, card_sq_eq_one_eq_succ] at h1
  omega

theorem card_le_of_sylow {C S : Subgroup G} {N : ℕ} (hk : ∀ P : Sylow 2 C, Nat.card P ≤ N)
    (hSC : S ≤ C) (hS : IsPGroup 2 S) : Nat.card S ≤ N := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hS' : IsPGroup 2 (S.subgroupOf C) := hS.of_equiv (subgroupOfEquivOfLe hSC).symm
  obtain ⟨P, hP⟩ := hS'.exists_le_sylow
  rw [← Nat.card_congr (subgroupOfEquivOfLe hSC).toEquiv]
  exact (Subgroup.card_le_of_le hP).trans (hk P)

theorem pinv_of_sylow {C S S₀ : Subgroup G} (hk : ∀ P : Sylow 2 C, Nat.card P = 2 ^ 8)
    (hSC : S ≤ C) (hS : Nat.card S = 2 ^ 8) (hS₀C : S₀ ≤ C) (hS₀ : PInv S₀) : PInv S := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨P⟩ := (inferInstance : Nonempty (Sylow 2 C))
  have hfac : (Nat.card C).factorization 2 = 8 := by
    have h1 := Sylow.card_eq_multiplicity P
    rw [hk P] at h1
    exact (Nat.pow_right_injective le_rfl h1).symm
  have e1 : S.subgroupOf C ≃* S := subgroupOfEquivOfLe hSC
  have e2 : S₀.subgroupOf C ≃* S₀ := subgroupOfEquivOfLe hS₀C
  have hcS : Nat.card (S.subgroupOf C) = 2 ^ (Nat.card C).factorization 2 := by
    rw [hfac, ← hS]
    exact Nat.card_congr e1.toEquiv
  have hcS₀ : Nat.card (S₀.subgroupOf C) = 2 ^ (Nat.card C).factorization 2 := by
    rw [hfac, ← hS₀.1]
    exact Nat.card_congr e2.toEquiv
  have e3 : S₀.subgroupOf C ≃* S.subgroupOf C :=
    Sylow.equiv (Sylow.ofCard (S₀.subgroupOf C) hcS₀) (Sylow.ofCard (S.subgroupOf C) hcS)
  exact hS₀.of_mulEquiv (e2.symm.trans (e3.trans e1))

end Sylow

variable {G : Type} [Group G] [Finite G] {L Q : Subgroup G} {n : ℕ}
  {θ : L ≃* alternatingGroup (Fin n)} {z : G}

theorem centHyp_of_config (c : Config G L Q n θ z) : CentHyp z := by
  have hsyl := sec4CentSylowCard_holds G L Q n θ z c
  have hle : ∀ P : Sylow 2 (centralizer ({z} : Set G)), Nat.card P ≤ 2 ^ 8 := by
    intro P
    by_cases h : IsASmall L n z
    · rw [(hsyl P).1 h]
      norm_num
    · exact ((hsyl P).2 h).le
  refine ⟨fun S hSC hS => card_le_of_sylow hle hSC hS, fun S hSC hS hS8 => ?_⟩
  by_cases hA : IsASmall L n z
  · have h7 := card_le_of_sylow (fun P => ((hsyl P).1 hA).le) hSC hS
    rw [hS8] at h7
    norm_num at h7
  have h8 : ∀ P : Sylow 2 (centralizer ({z} : Set G)), Nat.card P = 2 ^ 8 := fun P =>
    (hsyl P).2 hA
  rcases c.shape with hin | ⟨h9, u, huC, huO, hu2⟩
  · rcases c.n_cases with rfl | rfl | rfl | rfl
    · exact absurd ⟨Or.inl rfl, hin⟩ hA
    · exact absurd ⟨Or.inr rfl, hin⟩ hA
    · exact pinv_of_sylow h8 hSC hS8 sSyl_le_cent
        (pinv_sSyl (isHStar_inner c) fusR10 card_sq_rBar10)
    · exact pinv_of_sylow h8 hSC hS8 sSyl_le_cent
        (pinv_sSyl (isHStar_inner c) fusR11 card_sq_rBar11)
  · rcases (show n = 8 ∨ n = 9 by have := c.hn8; omega) with rfl | rfl
    · exact pinv_of_sylow h8 hSC hS8 sSyl_le_cent
        (pinv_sSyl (isHStar_outer c huC huO hu2) fusRS8 card_sq_rBarS8)
    · exact pinv_of_sylow h8 hSC hS8 sSyl_le_cent
        (pinv_sSyl (isHStar_outer c huC huO hu2) fusRS9 card_sq_rBarS9)

end CFSG.OddStandard.AltStdSmall4.Tower
