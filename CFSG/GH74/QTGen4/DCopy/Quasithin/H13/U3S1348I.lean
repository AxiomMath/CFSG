module

public import CFSG.Quasithin.H13.U3S1348I
public import CFSG.GH74.QTGen4.DCopy.Quasithin.H13.U3S135Gen
public import CFSG.GH74.QTGen4.DCopy.Quasithin.Vol2.Ch12Sec2Statements

public section

namespace CFSG.Quasithin.H13.U3

open Subgroup Equiv CFSG.Open CFSG.Blueprint CFSG.Quasithin CFSG.QuasithinUnique
open CFSG.Quasithin.H13.A6 CFSG.LieType.BorelTits

variable {G : Type} [Group G] [CFSG.GH74.QTGen4.Finite4 G] {T L V : Subgroup G}

theorem s134_mem_L1_of_three_F4 (h1332 : Stmt13_3_2_F4) (h1228 : Stmt12_2_8_F4)
    (S : A6.Setting134 G T L V)
    (he : Nonempty (↥L ⧸ CFSG.pCore 2 ↥L ≃* alternatingGroup (Fin 6))) {z : G}
    (hz : z ∈ fsuV1 T V) (hzL : z ∉ centralizer (L : Set G)) {x : G}
    (hxM : x ∈ normalizer (L : Set G)) (hxz : x ∈ centralizer ({z} : Set G))
    (hx3 : ∃ k : ℕ, x ^ 3 ^ k = 1) : x ∈ L₁Of L (fsuV1 T V) := by
  have hyp := hyp1223_of_F4 h1332 S.h13 S.irr

  have hxL : x ∈ L := by
    rcases h1228 G T L V hyp with h | h | ⟨⟨n, -, -, hz3, -⟩, -⟩
    · rw [← h]
      exact subset_closure ⟨hxM, hx3⟩
    · exfalso
      obtain ⟨e⟩ := he
      rcases h with he5 | hl
      · obtain ⟨e5⟩ := he5
        have h1 := Nat.card_congr (e.symm.trans e5).toEquiv
        rw [nat_card_alternatingGroup, nat_card_alternatingGroup, Nat.card_fin,
          Nat.card_fin] at h1
        revert h1
        decide
      · exact s134_not_L32 S hl
    · exfalso
      obtain ⟨e6⟩ := he
      have hs : IsSimpleGroup ↥(alternatingGroup (Fin 6)) :=
        alternatingGroup.isSimpleGroup (by simp)
      have hsQ : IsSimpleGroup (↥L ⧸ CFSG.pCore 2 ↥L) := (MulEquiv.isSimpleGroup_congr e6).2 hs
      have hna : ∃ a b : ↥L ⧸ CFSG.pCore 2 ↥L, a * b ≠ b * a := by
        obtain ⟨a, b, hab⟩ := alt6_nonabelian
        exact ⟨e6.symm a, e6.symm b, fun h => hab (by simpa using congrArg e6 h)⟩
      rcases (inferInstance : (center (↥L ⧸ CFSG.pCore 2 ↥L)).Normal).eq_bot_or_eq_top with
        h | h
      · rw [h, Subgroup.card_bot] at hz3
        omega
      · obtain ⟨a, b, hab⟩ := hna
        exact hab (mem_center_iff.1 (h ▸ mem_top b) a)

  have hxzV : x * S.zV = S.zV * x :=
    mem_centralizer_iff.1 (S.mem_ZV_iff.2 (Or.inr rfl)).2 x hxL
  have hxz' : x * z = z * x := mem_centralizer_singleton_iff.1 hxz
  obtain ⟨hzV, hψz⟩ := s134_psi_z S hz hzL
  have hxV1 : x ∈ centralizer (fsuV1 T V : Set G) := by
    refine mem_centralizer_iff.2 fun w hw => ?_
    obtain ⟨hwV, hwW⟩ := S.mem_V1_iff.1 hw
    have hcases := W1_cases _ (S.frame.ψ ⟨w, hwV⟩).2 hwW

    have hw' : w = 1 ∨ w = S.zV ∨ w = z ∨ w = z * S.zV := by
      have hψ1 : (S.frame.ψ ⟨S.zV, S.zV_mem_V⟩ : P6) = G6.allOnes 6 := by rw [S.psi_zV]
      have key : ∀ a b : G, ∀ (ha : a ∈ V) (hb : b ∈ V),
          (S.frame.ψ ⟨a, ha⟩ : P6) = S.frame.ψ ⟨b, hb⟩ → a = b := fun a b ha hb h =>
        congrArg Subtype.val (S.frame.ψ.injective (Subtype.ext h))
      have hmul : (S.frame.ψ ⟨z * S.zV, mul_mem hzV S.zV_mem_V⟩ : P6) =
          (S.frame.ψ ⟨z, hzV⟩ : P6) * G6.allOnes 6 := by
        rw [show (⟨z * S.zV, mul_mem hzV S.zV_mem_V⟩ : ↥V) = ⟨z, hzV⟩ * ⟨S.zV, S.zV_mem_V⟩
          from rfl, map_mul, Subgroup.coe_mul, hψ1]
      rcases hcases with h | h | h | h
      · left
        have h1 : S.frame.ψ ⟨w, hwV⟩ = 1 := Subtype.ext h
        exact congrArg Subtype.val ((MulEquiv.map_eq_one_iff _).1 h1)
      · exact Or.inr (Or.inl (key _ _ hwV S.zV_mem_V (h.trans hψ1.symm)))
      · rcases hψz with hz' | hz'
        · exact Or.inr (Or.inr (Or.inl (key _ _ hwV hzV (h.trans hz'.symm))))
        · refine Or.inr (Or.inr (Or.inr (key _ _ hwV (mul_mem hzV S.zV_mem_V) ?_)))
          rw [hmul, hz', h, allOnes_eq_mul]
          decide
      · rcases hψz with hz' | hz'
        · refine Or.inr (Or.inr (Or.inr (key _ _ hwV (mul_mem hzV S.zV_mem_V) ?_)))
          rw [hmul, hz', h, allOnes_eq_mul]
          decide
        · exact Or.inr (Or.inr (Or.inl (key _ _ hwV hzV (h.trans hz'.symm))))
    rcases hw' with rfl | rfl | rfl | rfl
    · rw [one_mul, mul_one]
    · exact hxzV.symm
    · exact hxz'.symm
    · calc z * S.zV * x = z * (S.zV * x) := by group
        _ = z * (x * S.zV) := by rw [hxzV]
        _ = (z * x) * S.zV := by group
        _ = (x * z) * S.zV := by rw [hxz']
        _ = x * (z * S.zV) := by group
  obtain ⟨k, hk⟩ := hx3
  exact mem_oTwoRes_of_odd (mem_inf.2 ⟨hxL, centralizer_le_normalizer _ hxV1⟩)
    (Odd.pow (by decide)) hk

theorem s134_I_not_le_M_F4 (h1332 : Stmt13_3_2_F4) (h1228 : Stmt12_2_8_F4)
    (S : A6.Setting134 G T L V)
    (he : Nonempty (↥L ⧸ CFSG.pCore 2 ↥L ≃* alternatingGroup (Fin 6))) {z : G}
    (hz : z ∈ fsuV1 T V) (hzL : z ∉ centralizer (L : Set G)) {H VH : Subgroup G}
    (hHz : InHz T L V z H) (hsolv : Group.IsSolvable ↥H) (hred : IsTwoReducedIn H VH)
    (hcR : r1Of T L V ⊓ centralizer (VH : Set G) = pCoreOf 2 H)
    (hJ : ¬ thompsonJ (r1Of T L V) ≤ centralizer (VH : Set G))
    {𝓗 𝓘 : Finset (Subgroup (MulAut (IntMod VH hred.2.2.1)))}
    (B : BlocksR (hV := hred.2.2.1) H (r1Of T L V) 𝓗 𝓘) (hne : 𝓘.Nonempty) (hcard : 𝓘.card ≤ 2) :
    ¬ conjClosure (thompsonJ (r1Of T L V)) H ≤ normalizer (L : Set G) := by
  intro hIM
  obtain ⟨-, -, hHzC, -, -⟩ := s134_inHz_facts S hHz
  have hIH : conjClosure (thompsonJ (r1Of T L V)) H ≤ H := conjClosure_le fun h hh j hj =>
    mul_mem (mul_mem hh ((((iSup₂_le fun _ hA => hA.1 :
      thompsonJ (r1Of T L V) ≤ r1Of T L V).trans (r1Of_le_T T L V)).trans
        (s134_inHz_facts S hHz).1.1) hj)) (inv_mem hh)
  obtain ⟨x, hxI, hx3, hxN, hx1⟩ := exists_three_elt_I B hne
  have hxL1 := s134_mem_L1_of_three_F4 h1332 h1228 S he hz hzL (hIM hxI) (hHzC (hIH hxI)) hx3
  have hxI' : convI hred.2.2.1 ⟨x, hxN⟩ ∈ ⨆ K ∈ 𝓘, K := by
    rw [← B.eq]
    exact convI_mem_autI _ hxI hxN
  obtain ⟨k, hk⟩ := hx3
  have hC := s134_odd_trivial S (s134Plus_L1 S he) hHz hsolv hred hcR hJ B hcard hxL1 hxN hxI'
    ⟨3 ^ k, Odd.pow (by decide), hk⟩
  exact hx1 ((convI_eq_one_iff _ _).2 hC)

end CFSG.Quasithin.H13.U3
