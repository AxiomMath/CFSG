module

public import CFSG.CGT.M24R.Interfaces
public import CFSG.CGT.M24S.NSDefs
public import CFSG.CGT.Timmesfeld75.Sec215Local
public import CFSG.GH74.Exceptional.LinearFourTwo

public section

namespace CFSG.CGT.M24R

open CFSG.CGT.Timmesfeld75 CFSG.CGT.M24S
open scoped MatrixGroups

@[expose] noncomputable def slEquivGLOfCardTwo {K : Type} [Field K] [Finite K]
    (hK : Nat.card K = 2) (n : ℕ) : SL(n, K) ≃* GL (Fin n) K :=
  MulEquiv.ofBijective (Matrix.SpecialLinearGroup.toGL : SL(n, K) →* GL (Fin n) K)
    ⟨Matrix.SpecialLinearGroup.toGL_injective, fun A => by
      have : Subsingleton Kˣ := by
        have hcard : Nat.card Kˣ = 1 := by rw [Nat.card_units, hK]
        exact (Nat.card_eq_one_iff_unique.mp hcard).1
      have hdet : (A : Matrix (Fin n) (Fin n) K).det = 1 := by
        have h1 : Matrix.GeneralLinearGroup.det A = 1 := Subsingleton.elim _ _
        have h2 := congrArg (fun u : Kˣ => (u : K)) h1
        simpa using h2
      refine ⟨⟨(A : Matrix (Fin n) (Fin n) K), hdet⟩, ?_⟩
      apply Units.ext
      rfl⟩

@[expose] noncomputable def sl4GF2EquivAlt8 : SL(4, GaloisField 2 1) ≃* alternatingGroup (Fin 8) :=
  have hK : Nat.card (GaloisField 2 1) = 2 := by simpa using GaloisField.card 2 1 one_ne_zero
  ((slEquivGLOfCardTwo hK 4).trans (CFSG.GH74.Exceptional.glEquivZModTwoOfCardTwo hK 4)).trans
    CFSG.GH74.Exceptional.alternatingEightEquivGLFourTwo.symm

variable {G : Type} [Group G]

theorem normalizer_eq_of_centralizer_eq {T H : Subgroup G} (h : Hyp T H) (hL : LocalFacts T H)
    (hC : Subgroup.centralizer (T : Set G) = T) : Subgroup.normalizer (T : Set G) = H := by
  rw [hL.normalizer_eq, hC, sup_eq_left.mpr h.le]

theorem nonempty_nQuot_equiv_alt8 {T H : Subgroup G} (h : Hyp T H)
    (hNT : Subgroup.normalizer (T : Set G) = H) :
    Nonempty (NQuot T ≃* alternatingGroup (Fin 8)) := by
  obtain ⟨_, e, -, -⟩ := h.nat
  subst hNT
  exact ⟨e.trans sl4GF2EquivAlt8⟩

theorem m24CtxHyp_conjSubgroup_of_type4 [Finite G] {T H : Subgroup G} (h : Hyp T H)
    (hL : LocalFacts T H) (hC : Subgroup.centralizer (T : Set G) = T)
    (hcompl : HasComplement T H) {x g : G} (hxN : x ∈ Subgroup.normalizer (T : Set G))
    (hxT : x ∉ T) (hxg : x ∈ conjSubgroup g T)
    (hcx : Nat.card ↥(T ⊓ Subgroup.centralizer ({x} : Set G)) = 4) :
    M24CtxHyp T (conjSubgroup g T) := by
  have hT := h.wc
  have hNT := normalizer_eq_of_centralizer_eq h hL hC
  have hx1 : x ≠ 1 := fun hx => hxT (hx ▸ T.one_mem)
  have hne : conjSubgroup g T ≠ T := fun he => hxT (he ▸ hxg)
  have hwc₁ : IsWC (conjSubgroup g T) := hT.conj g
  have hle : T ⊓ Subgroup.centralizer ({x} : Set G) ≤ normIn T (conjSubgroup g T) :=
    fun t ht => mem_normIn.2 ⟨ht.1, hwc₁.centralizer_le_normalizer hxg hx1 ht.2⟩
  have hLne : normIn T (conjSubgroup g T) ≠ ⊥ := by
    intro hb
    rw [hb, le_bot_iff] at hle
    rw [hle, Subgroup.card_bot] at hcx
    omega
  have c := Cfg.of_conj hT hne hLne
  have hxL₁ : x ∈ normIn (conjSubgroup g T) T := mem_normIn.2 ⟨hxg, hxN⟩
  have heq : T ⊓ Subgroup.centralizer ({x} : Set G) = normIn T (conjSubgroup g T) :=
    le_antisymm hle fun t ht => ⟨normIn_le _ _ ht,
      Subgroup.mem_centralizer_singleton_iff.2 (c.comm_L_L₁ ht hxL₁)⟩
  have hn1 : Nat.card (normIn T (conjSubgroup g T)) = 4 := by rw [← heq, hcx]
  exact
    { wc := hT
      card16 := hL.card_T
      inf_bot := hT.inf_conj_eq_bot hne
      conj := ⟨g, rfl⟩
      norm1 := hn1
      norm2 := by rw [← c.card_normIn_eq ⟨g, rfl⟩]; exact hn1
      cent_le := hL.centralizer_le
      cent_eq := hC
      trans := fun a ha ha1 b hb hb1 => by
        obtain ⟨k, hk, hkab⟩ := hL.transitive a ha ha1 b hb hb1
        exact ⟨k, hL.le_normalizer hk, hkab⟩
      quot := nonempty_nQuot_equiv_alt8 h hNT
      compl := by
        obtain ⟨K, -, hTK, hTKH⟩ := hcompl
        exact ⟨K, by rw [inf_comm]; exact hTK, hTKH.trans hNT.symm⟩ }

end CFSG.CGT.M24R
