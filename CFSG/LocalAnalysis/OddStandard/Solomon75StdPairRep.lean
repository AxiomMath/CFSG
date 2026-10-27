module

public import CFSG.LocalAnalysis.OddStandard.Solomon75StdPairEmb
public import CFSG.LocalAnalysis.OddStandard.Solomon75StdPermSL
public import CFSG.LocalAnalysis.OddStandard.Solomon75StdPermDeg

public section

namespace CFSG.OddStandard.Solomon75

open Equiv Equiv.Perm Subgroup CFSG CFSG.GH74.GLS AhatData

section CenterLe

variable {n : ℕ} {K : Type} [Group K]

theorem AhatData.CoverSetup.center_le_of_doubleCover (C : CoverSetup n K) {σ : Perm (Fin n)}
    {D : Subgroup K} (hD : D.map C.ρ = altFixOf σ) {f : ℕ} (hDc : IsDoubleCoverOfAlt ↥D f)
    (hf : f = n - σ.support.card) (hf2 : 2 ≤ f) : center K ≤ D := by
  intro w hw
  by_contra hwD
  have hw1 : w ≠ 1 := fun h => hwD (h ▸ D.one_mem)
  let φ : ↥D →* Perm (Fin n) := C.ρ.comp D.subtype
  have hinj : Function.Injective φ := by
    rw [← MonoidHom.ker_eq_bot_iff, eq_bot_iff]
    intro d hd
    rw [MonoidHom.mem_ker] at hd
    have hdc : (d : K) ∈ center K := (C.ρ_eq_one_iff).1 hd
    by_contra hd1
    have hd1' : (d : K) ≠ 1 := fun h => hd1 (by
      rw [Subgroup.mem_bot]
      exact Subtype.ext h)
    exact hwD ((C.center_eq_of_ne_one hdc hw hd1' hw1) ▸ d.2)
  have hrange : φ.range = altFixOf σ := by
    rw [MonoidHom.range_comp, Subgroup.range_subtype]
    exact hD
  have hcard : Nat.card ↥D = Nat.card ↥(altFixOf σ) := by
    rw [← hrange]
    exact Nat.card_congr (Equiv.ofInjective φ hinj)
  have h1 := card_doubleCover hf2 hDc
  have h2 := card_altFixOf_mul_two σ (by omega)
  rw [← hf] at h2
  have h3 := Nat.factorial_pos f
  omega

end CenterLe

section Rep

variable {G : Type} [Group G] [Finite G] [IsSimpleGroup G] {L L' : Subgroup G} {n : ℕ} {z a : G}
  (P : StdPair G L L' n z a) (M : AhatModel G n L) (M' : AhatModel G n L')

theorem StdPair.emb_mem_norm' {x : M.K} (hx : x ∈ fixSub (M.autOf a P.a_mem_norm)) :
    P.setup.emb M x ∈ normalizer (L' : Set G) :=
  P.setup'.mem_normalizer_of_mem_centralizer
    ((M.mem_fixSub_iff P.setup.pPrimeCore_eq_bot P.a_mem_norm x).1 hx)

@[expose] noncomputable def StdPair.rep (H : Subgroup M.K)
    (hH : H ≤ fixSub (M.autOf a P.a_mem_norm)) : ↥H →* Perm (Fin n) :=
  (M'.permHom P.setup'.hn).comp
    (((P.setup.emb M).comp H.subtype).codRestrict (normalizer (L' : Set G))
      (fun x => P.emb_mem_norm' M (hH x.2)))

variable {M M'} {H : Subgroup M.K} {hH : H ≤ fixSub (M.autOf a P.a_mem_norm)}

theorem StdPair.rep_apply (x : ↥H) :
    P.rep M M' H hH x = M'.perm (P.setup.emb M x) (P.emb_mem_norm' M (hH x.2)) := rfl

theorem StdPair.rep_eq_perm (x : ↥H) {c : G} (hxc : P.setup.emb M x = c)
    (hc : c ∈ normalizer (L' : Set G)) : P.rep M M' H hH x = M'.perm c hc :=
  M'.perm_congr hxc _ _

theorem StdPair.rep_eq_one_iff (x : ↥H) :
    P.rep M M' H hH x = 1 ↔ P.setup.emb M x ∈ centralizer (L' : Set G) := by
  rw [P.rep_apply]
  exact P.setup'.perm_eq_one_iff M' _

theorem StdPair.rep_comm {r : M.K} (hr : ∀ x ∈ H, x * r = r * x)
    (hrN : P.setup.emb M r ∈ normalizer (L' : Set G)) (x : ↥H) :
    P.rep M M' H hH x * M'.perm (P.setup.emb M r) hrN =
      M'.perm (P.setup.emb M r) hrN * P.rep M M' H hH x := by
  have hn := P.setup'.hn
  rw [P.rep_apply, ← M'.perm_mul hn (P.emb_mem_norm' M (hH x.2)) hrN,
    ← M'.perm_mul hn hrN (P.emb_mem_norm' M (hH x.2))]
  exact M'.perm_congr ((M.emb_commute_iff _ _ _).2 (hr x x.2)) _ _

end Rep

section C2C3

variable {G : Type} [Group G] [Finite G] [IsSimpleGroup G] {L L' : Subgroup G} {n : ℕ} {z a : G}
  (P : StdPair G L L' n z a)

theorem StdPair.perm_a_sq (M : AhatModel G n L) :
    M.perm a P.a_mem_norm * M.perm a P.a_mem_norm = 1 :=
  M.perm_mul_self_eq_one P.setup.hn P.a_mem_norm P.a_mul_self

theorem StdPair.perm_z_sq (M' : AhatModel G n L') :
    M'.perm z P.z_mem_norm' * M'.perm z P.z_mem_norm' = 1 :=
  M'.perm_mul_self_eq_one P.setup'.hn P.z_mem_norm' P.z_mul_self

theorem StdPair.perm_a_ne_one (M : AhatModel G n L) : M.perm a P.a_mem_norm ≠ 1 := fun h =>
  P.a_not_cent ((P.setup.perm_eq_one_iff M _).1 h)

theorem StdPair.perm_z_ne_one (M' : AhatModel G n L') : M'.perm z P.z_mem_norm' ≠ 1 := fun h =>
  P.z_not_cent' ((P.setup'.perm_eq_one_iff M' _).1 h)

theorem StdPair.two_le_transCount (M : AhatModel G n L) (M' : AhatModel G n L') :
    2 ≤ transCount (M.perm a P.a_mem_norm) := by
  have hn := P.setup.hn
  have hσ2 := P.perm_a_sq M
  have hσ'2 := P.perm_z_sq M'
  have hσ1 := P.perm_a_ne_one M
  have hind := M.induces_perm hn a P.a_mem_norm
  generalize M.perm a P.a_mem_norm = σ at hσ2 hσ1 hind ⊢
  by_contra hlt
  push Not at hlt
  have hsupp := card_support_eq_two_mul_transCount hσ2
  have hm0 : transCount σ ≠ 0 := by
    intro h0
    rw [h0] at hsupp
    exact hσ1 (Equiv.Perm.card_support_eq_zero.1 (by omega))
  have hm1 : transCount σ = 1 := by omega
  rw [hm1] at hsupp
  have hf : 5 ≤ n - 2 * 1 := by omega
  obtain ⟨hDfix, hDcov, hDmap⟩ :=
    hind.fixedCompOf_isDoubleCover M.C hn hσ2 hsupp hf
  set D := M.C.fixedCompOf σ with hD
  have hcen : center M.K ≤ D :=
    M.C.center_le_of_doubleCover hDmap hDcov (by omega) (by omega)
  have hzD : P.setup.zK M ∈ D := hcen (P.setup.zK_mem_center M)
  have hzc : (⟨P.setup.zK M, hzD⟩ : ↥D) ∈ center ↥D := by
    rw [Subgroup.mem_center_iff]
    intro d
    exact Subtype.ext (Subgroup.mem_center_iff.1 (P.setup.zK_mem_center M) d)
  have hι : P.rep M M' D hDfix ⟨P.setup.zK M, hzD⟩ = M'.perm z P.z_mem_norm' :=
    P.rep_eq_perm _ (P.setup.emb_zK M) _
  have h := two_mul_le_card_support_of_doubleCover hf hDcov (P.rep M M' D hDfix) hzc
    (by rw [hι]; exact P.perm_z_ne_one M')
  rw [hι, card_support_eq_two_mul_transCount hσ'2] at h
  have h1 := card_eq_of_involution hσ2
  have h2 := card_eq_of_involution hσ'2
  omega

theorem StdPair.even_transCount' (M : AhatModel G n L) (M' : AhatModel G n L') :
    Even (transCount (M'.perm z P.z_mem_norm')) := by
  have hn := P.setup.hn
  have hσ2 := P.perm_a_sq M
  have hσ'2 := P.perm_z_sq M'
  obtain ⟨r, hr⟩ := exists_isPairLift M.C hσ2 (card_support_eq_two_mul_transCount hσ2)
    (P.two_le_transCount M M')
  obtain ⟨hsq, hcomm⟩ := P.emb_pairLift M hr
  have hrN : P.setup.emb M r ∈ normalizer (L' : Set G) :=
    P.setup'.mem_normalizer_of_mem_centralizer (Subgroup.mem_centralizer_singleton_iff.2 hcomm)
  have hππ : M'.perm (P.setup.emb M r) hrN * M'.perm (P.setup.emb M r) hrN =
      M'.perm z P.z_mem_norm' := by
    rw [← M'.perm_mul P.setup'.hn hrN hrN]
    exact M'.perm_congr hsq _ _
  have h4 : (M'.perm (P.setup.emb M r) hrN * M'.perm (P.setup.emb M r) hrN) *
      (M'.perm (P.setup.emb M r) hrN * M'.perm (P.setup.emb M r) hrN) = 1 := by
    rw [hππ]
    exact hσ'2
  refine even_of_sq_involution h4 (k := transCount (M'.perm z P.z_mem_norm')) ?_
  rw [hππ]
  exact card_support_eq_two_mul_transCount hσ'2

end C2C3

end CFSG.OddStandard.Solomon75
