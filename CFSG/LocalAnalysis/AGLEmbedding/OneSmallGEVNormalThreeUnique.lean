module

public import CFSG.LocalAnalysis.AGLEmbedding.OneSmallGEVNormalThreeDiag
import CFSG.LocalAnalysis.AGLEmbedding.ResidualToolsAux

public section

namespace CFSG.AGLEmbedding

open CFSG.Open CFSG.Quasithin CFSG.QuasithinUnique CFSG.RankThreeCoreUniqueness.Helpers

variable {G : Type} [Group G] [Finite G] {p : ℕ} {P : Sylow p G} {M H R : Subgroup G}

omit [Finite G] in
theorem mem_centralizer_of_conj_mem_map {X : Type*} [Group X] {L : Subgroup X} {g x : X}
    (hx : g * x * g⁻¹ ∈ Subgroup.centralizer
      ((L.map (MulAut.conj g).toMonoidHom : Subgroup X) : Set X)) :
    x ∈ Subgroup.centralizer (L : Set X) := by
  rw [Subgroup.mem_centralizer_iff] at hx ⊢
  intro y hy
  have h1 := hx (g * y * g⁻¹) ⟨y, hy, rfl⟩
  have h2 : g * (y * x) * g⁻¹ = g * (x * y) * g⁻¹ := by
    calc g * (y * x) * g⁻¹ = g * y * g⁻¹ * (g * x * g⁻¹) := by group
      _ = g * x * g⁻¹ * (g * y * g⁻¹) := h1
      _ = g * (x * y) * g⁻¹ := by group
  simpa using h2

namespace D1MSideAt

variable {S : Subgroup G}

theorem barM_eq_of_mem_component (h : D1MSideAt M S) (hp : p.Prime)
    (hp2 : p ≠ 2) {z : G} (hzM : z ∈ M) (hz : IsPGroup p (Subgroup.zpowers z))
    (hCz : M ⊓ Subgroup.centralizer ({z} : Set G) ≤
      Subgroup.normalizer (S : Set G)) {A : Subgroup (↥M ⧸ CFSG.pCore 2 ↥M)}
    (hA : IsComponentOf A ⊤) (hzA : QuotientGroup.mk' (CFSG.pCore 2 ↥M) ⟨z, hzM⟩ ∈ A)
    {L' : Subgroup G} (hL' : IsWeakSBlock M S L') : barM M L' = A := by
  by_contra hne
  exact h.not_mem_centralizer_block hp hp2 hzM hz hCz hL'
    (le_centralizer_of_component_ne hA hL'.component (Ne.symm hne) hzA)


theorem false_of_rep_inv (h : D1MSideAt M S) (hp : p.Prime) (hp2 : p ≠ 2)
    {z : G} (hzM : z ∈ M) (hz : IsPGroup p (Subgroup.zpowers z))
    (hCz : M ⊓ Subgroup.centralizer ({z} : Set G) ≤
      Subgroup.normalizer (S : Set G)) {L : Subgroup G}
    (hL : IsWeakSBlock M S L) {r : G} (hrM : r ∈ M) (hr3 : r ^ 3 = 1)
    (hrL : QuotientGroup.mk' (CFSG.pCore 2 ↥M) ⟨r, hrM⟩ ∈ barM M L)
    (hrc : (QuotientGroup.mk' (CFSG.pCore 2 ↥M) ⟨r, hrM⟩)⁻¹ *
      QuotientGroup.mk' (CFSG.pCore 2 ↥M) ⟨z, hzM⟩ ∈
      Subgroup.centralizer (barM M L : Set (↥M ⧸ CFSG.pCore 2 ↥M)))
    {n : G} (hnM : n ∈ M) (hnz : n * z * n⁻¹ = z) (hnr : n * r * n⁻¹ = r⁻¹) : False := by
  set mk := QuotientGroup.mk' (CFSG.pCore 2 ↥M) with hmk
  set zb := mk ⟨z, hzM⟩ with hzb
  set rb := mk ⟨r, hrM⟩ with hrb
  set nb := mk ⟨n, hnM⟩ with hnb
  have hnC : n ∈ Subgroup.centralizer ({z} : Set G) := by
    rw [Subgroup.mem_centralizer_singleton_iff]
    calc n * z = n * z * n⁻¹ * n := by group
      _ = z * n := by rw [hnz]
  have hnS : n ∈ Subgroup.normalizer (S : Set G) := hCz ⟨hnM, hnC⟩
  have hL₂ := hL.map_conj hnM hnS
  have hnzb : nb * zb * nb⁻¹ = zb := by
    rw [hnb, hzb, ← map_inv, ← map_mul, ← map_mul]
    congr 1
    exact Subtype.ext hnz
  have hnrb : nb * rb * nb⁻¹ = rb⁻¹ := by
    rw [hnb, hrb, ← map_inv, ← map_mul, ← map_mul, ← map_inv]
    congr 1
    exact Subtype.ext hnr
  have hbar₂ : barM M (L.map (MulAut.conj n).toMonoidHom) =
      (barM M L).map (MulAut.conj nb).toMonoidHom := barM_map_conj hnM L
  have hr₂ : rb⁻¹ ∈ barM M (L.map (MulAut.conj n).toMonoidHom) := by
    rw [hbar₂, ← hnrb]; exact ⟨rb, hrL, rfl⟩
  have hrc₂ : rb * zb ∈ Subgroup.centralizer
      (barM M (L.map (MulAut.conj n).toMonoidHom) : Set (↥M ⧸ CFSG.pCore 2 ↥M)) := by
    rw [Subgroup.mem_centralizer_iff]
    rintro _ hy
    rw [hbar₂] at hy
    obtain ⟨y, hy, rfl⟩ := hy
    have hcy := Subgroup.mem_centralizer_iff.mp hrc y hy
    have e1 : rb * zb = nb * (rb⁻¹ * zb) * nb⁻¹ := by
      calc rb * zb = (nb * rb * nb⁻¹)⁻¹ * (nb * zb * nb⁻¹) := by rw [hnrb, hnzb, inv_inv]
        _ = nb * (rb⁻¹ * zb) * nb⁻¹ := by group
    simp only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply]
    rw [e1]
    calc nb * y * nb⁻¹ * (nb * (rb⁻¹ * zb) * nb⁻¹) = nb * (y * (rb⁻¹ * zb)) * nb⁻¹ := by group
      _ = nb * ((rb⁻¹ * zb) * y) * nb⁻¹ := by rw [hcy]
      _ = nb * (rb⁻¹ * zb) * nb⁻¹ * (nb * y * nb⁻¹) := by group
  have hzC : zb ∈ Subgroup.centralizer (barM M L : Set (↥M ⧸ CFSG.pCore 2 ↥M)) := by
    by_cases heq : barM M (L.map (MulAut.conj n).toMonoidHom) = barM M L
    · rw [heq] at hrc₂
      have hr2 : rb * rb ∈ Subgroup.centralizer (barM M L : Set (↥M ⧸ CFSG.pCore 2 ↥M)) := by
        have := Subgroup.mul_mem _ hrc₂ (Subgroup.inv_mem _ hrc)
        simpa [mul_assoc] using this
      have hrb3 : rb ^ 3 = 1 := by
        rw [hrb, ← map_pow]
        have : (⟨r, hrM⟩ : M) ^ 3 = 1 := Subtype.ext (by simpa using hr3)
        rw [this, map_one]
      have hr1 : rb ∈ Subgroup.centralizer (barM M L : Set (↥M ⧸ CFSG.pCore 2 ↥M)) := by
        have h4 : rb = (rb * rb) * (rb * rb) := by
          calc rb = rb ^ 3 * rb := by rw [hrb3, one_mul]
            _ = (rb * rb) * (rb * rb) := by rw [pow_succ, pow_two]; group
        rw [h4]
        exact Subgroup.mul_mem _ hr2 hr2
      have := Subgroup.mul_mem _ hr1 hrc
      simpa using this
    ·
      have hr₂' : rb ∈ barM M (L.map (MulAut.conj n).toMonoidHom) := by
        simpa using Subgroup.inv_mem _ hr₂
      have hr1 : rb ∈ Subgroup.centralizer (barM M L : Set (↥M ⧸ CFSG.pCore 2 ↥M)) :=
        le_centralizer_of_component_ne hL₂.component hL.component heq hr₂'
      have := Subgroup.mul_mem _ hr1 hrc
      simpa using this
  exact h.not_mem_centralizer_block hp hp2 hzM hz hCz hL hzC

end D1MSideAt

theorem D1PhaseThree.barM_eq_of_mem_component (h : D1PhaseThree p P M H R) (hp : p.Prime)
    (hp2 : p ≠ 2) {z : G} (hzM : z ∈ M) (hz : IsPGroup p (Subgroup.zpowers z))
    (hCz : Subgroup.centralizer ({z} : Set G) ≤ H) {A : Subgroup (↥M ⧸ CFSG.pCore 2 ↥M)}
    (hA : IsComponentOf A ⊤) (hzA : QuotientGroup.mk' (CFSG.pCore 2 ↥M) ⟨z, hzM⟩ ∈ A)
    {L' : Subgroup G} (hL' : IsWeakSBlock M (pCoreOf 2 H) L') : barM M L' = A :=
  h.toMSideAt.barM_eq_of_mem_component hp hp2 hzM hz (fun _ hx => localGroup_le_normalizer_pCoreOf 2 H (hCz hx.2))
    hA hzA hL'

theorem D1PhaseThree.false_of_rep_inv (h : D1PhaseThree p P M H R) (hp : p.Prime) (hp2 : p ≠ 2)
    {z : G} (hzM : z ∈ M) (hz : IsPGroup p (Subgroup.zpowers z))
    (hCz : Subgroup.centralizer ({z} : Set G) ≤ H) {L : Subgroup G}
    (hL : IsWeakSBlock M (pCoreOf 2 H) L) {r : G} (hrM : r ∈ M) (hr3 : r ^ 3 = 1)
    (hrL : QuotientGroup.mk' (CFSG.pCore 2 ↥M) ⟨r, hrM⟩ ∈ barM M L)
    (hrc : (QuotientGroup.mk' (CFSG.pCore 2 ↥M) ⟨r, hrM⟩)⁻¹ *
      QuotientGroup.mk' (CFSG.pCore 2 ↥M) ⟨z, hzM⟩ ∈
      Subgroup.centralizer (barM M L : Set (↥M ⧸ CFSG.pCore 2 ↥M)))
    {n : G} (hnM : n ∈ M) (hnz : n * z * n⁻¹ = z) (hnr : n * r * n⁻¹ = r⁻¹) : False :=
  h.toMSideAt.false_of_rep_inv hp hp2 hzM hz (fun _ hx => localGroup_le_normalizer_pCoreOf 2 H (hCz hx.2))
    hL hrM hr3 hrL hrc hnM hnz hnr

end CFSG.AGLEmbedding
