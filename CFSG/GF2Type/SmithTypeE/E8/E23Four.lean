module

public import CFSG.GF2Type.SmithTypeE.E8.ModAct
public import CFSG.GF2Type.SmithTypeE.E8.Qa

public section

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent
  instCommGroupOfIsSimpleGroupOfIsNilpotent

namespace CFSG.GF2Type.SmithTypeE.E8

open Subgroup CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.Open CFSG.LargeExtraspecial
  CFSG.LargeExtraspecial.S14
open CFSG.LieType.Steinberg.Minuscule (e7Data)
open CFSG.HardMathSupport.Cooperstein.Coordinator.Survivors (e7Rep56 e7Y56 e7n6)
open CFSG.SeitzReduction (highRoot)
open CFSG.SeitzReduction.EPilot (pinnedElt)
open CFSG.LargeExtraspecial.S14.SME (inv_eq_of_isConj mem_Qa_iff mem_Qa_symm mem_M_conj_iff
  isConj_of_cl_eq)


@[expose] def InComm (r : ↥(adjointGroup .E7 (ZMod 2))) (w : Fin e7Data.d →₀ ZMod 2) : Prop :=
  ∃ c, e7Rep56 (ZMod 2) r c - c = w

structure E23FourFacts8 : Prop where
  tv_invol : ∀ r : ↥(adjointGroup .E7 (ZMod 2)), IsRootInvol r → r * r = 1
  word : ∀ r : ↥(adjointGroup .E7 (ZMod 2)), IsRootInvol r → ∀ w ∈ weightVec, ∀ w' ∈ weightVec,
    InComm r w → InComm r w' →
      ∃ l : List ↥(adjointGroup .E7 (ZMod 2)), (∀ s ∈ l, IsRootInvol s ∧ s * r = r * s) ∧
        e7Rep56 (ZMod 2) l.prod w = w'
  plane : ∀ r r' : ↥(adjointGroup .E7 (ZMod 2)), IsRootInvol r → IsRootInvol r' →
    ¬ r * r' = r' * r → ¬ r * r' * r = r' * r * r' →
      ∃ w ∈ weightVec, InComm r w ∧ e7Rep56 (ZMod 2) r' w = w ∧ ¬ InComm r' w

variable {G : Type} [Group G] [Finite G]

theorem acts_inv {S : Setting G} {φ : S.Qt ≃ₗ[ZMod 2] (Fin e7Data.d →₀ ZMod 2)} {g : G}
    {T : ↥(adjointGroup .E7 (ZMod 2))} (hgM : g ∈ S.M) (hg : Acts S φ g T)
    (hT : ∀ v, e7Rep56 (ZMod 2) T (e7Rep56 (ZMod 2) T v) = v) : Acts S φ g⁻¹ T := by
  intro u hu
  have hu' : g⁻¹ * u * g ∈ S.QG := by
    simpa using S.conj_mem_QG (S.M.inv_mem hgM) hu
  have h1 := hg (g⁻¹ * u * g) hu'
  rw [show g * (g⁻¹ * u * g) * g⁻¹ = u by group] at h1
  rw [h1, hT, inv_inv]

theorem acts_one_of_mem_QG {S : Setting G} {φ : S.Qt ≃ₗ[ZMod 2] (Fin e7Data.d →₀ ZMod 2)}
    {q : G} (hq : q ∈ S.QG) : Acts S φ q 1 := by
  intro u hu
  rw [cl_conj_of_mem_QG' hq hu, rep_one_apply]

theorem acts_mul_of_mem_QG {S : Setting G} {φ : S.Qt ≃ₗ[ZMod 2] (Fin e7Data.d →₀ ZMod 2)}
    {q m : G} {T : ↥(adjointGroup .E7 (ZMod 2))} (hq : q ∈ S.QG) (hmM : m ∈ S.M)
    (hm : Acts S φ m T) : Acts S φ (q * m) T := by
  have := (acts_one_of_mem_QG (φ := φ) hq).mul hmM hm
  rwa [one_mul] at this

theorem acts_conj_of_comm {S : Setting G} {φ : S.Qt ≃ₗ[ZMod 2] (Fin e7Data.d →₀ ZMod 2)}
    {g m : G} {T H : ↥(adjointGroup .E7 (ZMod 2))} (hgM : g ∈ S.M) (hmM : m ∈ S.M)
    (hg : Acts S φ g T) (hm : Acts S φ m H) (hHH : H * H = 1) (hc : H * T = T * H) :
    Acts S φ (m * g * m⁻¹) T := by
  have hH : ∀ v, e7Rep56 (ZMod 2) H (e7Rep56 (ZMod 2) H v) = v := fun v => by
    rw [← rep_mul_apply, hHH, rep_one_apply]
  have h := (hm.mul hgM hg).mul (S.M.inv_mem hmM) (acts_inv hmM hm hH)
  have e : H * T * H = T := by rw [hc, mul_assoc, hHH, mul_one]
  rwa [e] at h

theorem exists_centralizer_word (hF : E23FourFacts8) (h34b : SmithE8E34b) [IsSimpleGroup G]
    (S : Setting G) (hw : S.width = 28) (hU : LieModel S.Mbar .E7 0 2 1)
    {φ : S.Qt ≃ₗ[ZMod 2] (Fin e7Data.d →₀ ZMod 2)}
    (h5 : ∀ s : ↥(adjointGroup .E7 (ZMod 2)), ∃ m ∈ S.M, Acts S φ m s)
    {x : G} (hx : IsConj S.z x) (hxM : x ∈ S.M) (hxQ : x ∉ S.QG)
    {r : ↥(adjointGroup .E7 (ZMod 2))} (hr : IsRootInvol r) (hA : Acts S φ x r) :
    ∀ l : List ↥(adjointGroup .E7 (ZMod 2)), (∀ s ∈ l, IsRootInvol s ∧ s * r = r * s) →
      ∃ m ∈ S.M, m * x = x * m ∧ Acts S φ m l.prod := by
  have hrr := hF.tv_invol r hr
  have hAA : ∀ v, e7Rep56 (ZMod 2) r (e7Rep56 (ZMod 2) r v) = v := fun v => by
    rw [← rep_mul_apply, hrr, rep_one_apply]
  have hxi := inv_eq_of_isConj S hx
  intro l
  induction l with
  | nil =>
    intro _
    exact ⟨1, S.M.one_mem, by simp, fun u hu => by simp [rep_one_apply]⟩
  | cons s l ih =>
    intro hw'
    obtain ⟨m₀, hm₀M, hm₀x, hm₀⟩ := ih (fun s' hs' => hw' s' (List.mem_cons_of_mem _ hs'))
    obtain ⟨hs, hcomm⟩ := hw' s (List.mem_cons_self ..)
    obtain ⟨m_s, hm_sM, hm_s⟩ := h5 s
    have hx'c : IsConj S.z (m_s * x * m_s⁻¹) := hx.trans (isConj_iff.mpr ⟨m_s, rfl⟩)
    have hx'M : m_s * x * m_s⁻¹ ∈ S.M :=
      S.M.mul_mem (S.M.mul_mem hm_sM hxM) (S.M.inv_mem hm_sM)
    have hx'A : Acts S φ (m_s * x * m_s⁻¹) r :=
      acts_conj_of_comm hxM hm_sM hA hm_s (hF.tv_invol s hs) hcomm
    have hxx'Q : x⁻¹ * (m_s * x * m_s⁻¹) ∈ S.QG := by
      rw [hxi]
      exact mem_QG_of_acts (S.M.mul_mem hxM hx'M) (hA.mul hx'M hx'A) fun v => by
        rw [rep_mul_apply, hAA]
    obtain ⟨q, hqQ, hq⟩ := h34b G S hw hU x _ hx hx'c hxM hxQ hxx'Q
    have hm'x : (q * m_s) * x = x * (q * m_s) := by
      calc (q * m_s) * x = q * (m_s * x * m_s⁻¹) * m_s := by group
        _ = q * (q⁻¹ * x * q) * m_s := by rw [hq]
        _ = x * (q * m_s) := by group
    have hm'M : q * m_s ∈ S.M := S.M.mul_mem (S.QG_le_M hqQ) hm_sM
    have hm' : Acts S φ (q * m_s) s := acts_mul_of_mem_QG hqQ hm_sM hm_s
    have hfin := hm'.mul hm₀M hm₀
    refine ⟨q * m_s * m₀, S.M.mul_mem hm'M hm₀M, ?_, by simpa using hfin⟩
    calc q * m_s * m₀ * x = q * m_s * (m₀ * x) := by group
      _ = q * m_s * (x * m₀) := by rw [hm₀x]
      _ = (q * m_s * x) * m₀ := by group
      _ = x * (q * m_s) * m₀ := by rw [hm'x]
      _ = x * (q * m_s * m₀) := by group

theorem exists_mem_Qa_of_class (hF : E23FourFacts8) (h33 : SmithE8E33) (h34a : SmithE8E34a)
    (h34b : SmithE8E34b) [IsSimpleGroup G] (S : Setting G) (hw : S.width = 28)
    (hU : LieModel S.Mbar .E7 0 2 1) {φ : S.Qt ≃ₗ[ZMod 2] (Fin e7Data.d →₀ ZMod 2)}
    (h2a : ∀ c : G, IsConj S.z c → c ∈ S.QG → c ≠ S.z → φ (S.cl c) ∈ weightVec)
    (h5 : ∀ s : ↥(adjointGroup .E7 (ZMod 2)), ∃ m ∈ S.M, Acts S φ m s)
    {g : G} (hxM : g * S.z * g⁻¹ ∈ S.M) (hxQ : g * S.z * g⁻¹ ∉ S.QG)
    {r : ↥(adjointGroup .E7 (ZMod 2))} (hr : IsRootInvol r)
    (hA : Acts S φ (g * S.z * g⁻¹) r) {w : Fin e7Data.d →₀ ZMod 2} (hwW : w ∈ weightVec)
    (hEw : InComm r w) :
    ∃ b : G, IsConj S.z b ∧ b ∈ S.QG ∧ φ (S.cl b) = w ∧ b ∈ S.Qa g := by
  have hx : IsConj S.z (g * S.z * g⁻¹) := isConj_iff.mpr ⟨g, rfl⟩
  obtain ⟨v, hv, hvQ, hvQa⟩ := h33 G S hw hU g hxM hxQ
  have hvz : v ≠ S.z := by
    rintro rfl
    exact SMF.conj_z_not_mem_QG S hxQ ((mem_Qa_iff S g S.z).mp hvQa)
  have hv1 := h2a v hv hvQ hvz
  have hcomm := mem_commQt_of_mem_Qa h34a S hw hU hxM hxQ hvQ hvQa
  obtain ⟨c, hc⟩ := exists_eq_of_mem_commQt hxM hA hcomm
  obtain ⟨l, hl, hlw⟩ := hF.word r hr _ hv1 w hwW ⟨c, hc.symm⟩ hEw
  obtain ⟨m, hmM, hmx, hmw⟩ := exists_centralizer_word hF h34b S hw hU h5 hx hxM hxQ hr hA l hl
  have hm' : g⁻¹ * m * g ∈ S.M := (mem_M_conj_iff S g m).mpr hmx
  have hvg : g⁻¹ * v * g ∈ S.QG := (mem_Qa_iff S g v).mp hvQa
  refine ⟨m * v * m⁻¹, hv.trans (isConj_iff.mpr ⟨m, rfl⟩), S.conj_mem_QG hmM hvQ, ?_, ?_⟩
  · rw [hmw v hvQ, hlw]
  · rw [mem_Qa_iff, show g⁻¹ * (m * v * m⁻¹) * g =
      (g⁻¹ * m * g) * (g⁻¹ * v * g) * (g⁻¹ * m * g)⁻¹ by group]
    exact S.conj_mem_QG hm' hvg

theorem smithE8E23Four_of (hF : E23FourFacts8) (hM : SmithE8Model) (h33 : SmithE8E33)
    (h34a : SmithE8E34a) (h34b : SmithE8E34b) (h24 : SmithE8E24) : SmithE8E23Four := by
  intro G _ _ _ S hw hU x y hx hy hxM hyM hxQ hyQ hxyQ hxy2Q hxy4Q
  obtain ⟨φ, ψ, ⟨hE, h2a, -, -⟩, h4⟩ := hM G S hw hU
  have h5 := exists_acts_of_equiv hE
  obtain ⟨r, hr, hA⟩ : ∃ r : ↥(adjointGroup .E7 (ZMod 2)), IsRootInvol r ∧ Acts S φ x r :=
    ⟨_, h4 x hxM hx hxQ, acts_of_equiv hE hxM⟩
  obtain ⟨r', hr', hB⟩ : ∃ r : ↥(adjointGroup .E7 (ZMod 2)), IsRootInvol r ∧ Acts S φ y r :=
    ⟨_, h4 y hyM hy hyQ, acts_of_equiv hE hyM⟩
  have hAA := hA.invol hx hxM
  have hBB := hB.invol hy hyM
  have hxi := inv_eq_of_isConj S hx
  have hyi := inv_eq_of_isConj S hy
  have hkl : r ≠ r' := by
    rintro rfl
    exact hxyQ (mem_QG_of_acts (S.M.mul_mem hxM hyM) (hA.mul hyM hB) fun v => by
      rw [rep_mul_apply, hAA])
  have hncomm : ¬ r * r' = r' * r := fun hc => hxy2Q (sq_mem_of_comm hxM hyM hA hB hAA hBB hc)
  have hnbraid : ¬ r * r' * r = r' * r * r' := by
    intro hbr
    apply hxyQ
    have h3 := cube_mem_of_braid hxM hyM hA hB hAA hBB hbr
    have e : (x * y) ^ 4 = (x * y) * (x * y) ^ 3 := pow_succ' (x * y) 3
    have := S.QG.mul_mem hxy4Q (S.QG.inv_mem h3)
    rwa [e, mul_inv_cancel_right] at this
  obtain ⟨w, hwW, hEw, hfix, hnEw⟩ := hF.plane r r' hr hr' hncomm hnbraid
  obtain ⟨gx, hgx⟩ := isConj_iff.mp hx
  obtain ⟨gy, hgy⟩ := isConj_iff.mp hy
  obtain ⟨b, hb, hbQ, hbw, hbx⟩ := exists_mem_Qa_of_class hF h33 h34a h34b S hw hU h2a h5
    (g := gx) (hgx ▸ hxM) (hgx ▸ hxQ) hr (hgx ▸ hA) hwW hEw
  have hfixy := fixQt_eq_of_smithE8E34a h34a S hw hU hy hyM hyQ
  have hby : y * b = b * y := by
    refine S.commute_of_cl_mem_fixQt hyM hfixy hbQ ?_
    rw [S.cl_mem_fixQt_iff hyM hbQ]
    apply φ.injective
    rw [hB b hbQ, hbw, hfix]
  have hbQy : b ∉ S.Qa gy := by
    intro hbQa
    have hcomm := mem_commQt_of_mem_Qa h34a S hw hU (g := gy) (hgy ▸ hyM) (hgy ▸ hyQ) hbQ hbQa
    rw [hgy] at hcomm
    obtain ⟨c, hc⟩ := exists_eq_of_mem_commQt hyM hB hcomm
    exact hnEw ⟨c, hc.symm.trans hbw⟩
  obtain ⟨gb, hgb⟩ := isConj_iff.mp hb
  have hbx' : gx⁻¹ * (gb * S.z * gb⁻¹) * gx ∈ S.QG := by
    rw [hgb]
    exact (mem_Qa_iff S gx b).mp hbx
  have hbxne : gb * S.z * gb⁻¹ ≠ gx * S.z * gx⁻¹ := by
    rw [hgb, hgx]
    exact fun h => hxQ (h ▸ hbQ)
  have hxQb : gb⁻¹ * x * gb ∈ S.QG := by
    have := mem_Qa_symm S hbx' hbxne
    rwa [hgx] at this
  have hyQb : gb⁻¹ * y * gb ∉ S.QG := by
    intro hyb
    have hQ : gb⁻¹ * (gy * S.z * gy⁻¹) * gb ∈ S.QG := by rwa [hgy]
    have hne : gy * S.z * gy⁻¹ ≠ gb * S.z * gb⁻¹ := by
      rw [hgy, hgb]
      exact fun h => hyQ (h ▸ hbQ)
    have := mem_Qa_symm S hQ hne
    rw [hgb] at this
    exact hbQy ((mem_Qa_iff S gy b).mpr this)
  have hy₁ : IsConj S.z (gb⁻¹ * y * gb) :=
    isConj_iff.mpr ⟨gb⁻¹ * gy, by rw [← hgy]; group⟩
  have hy₁M : gb⁻¹ * y * gb ∈ S.M := by
    rw [mem_M_conj_iff, hgb]
    exact hby
  have hx₁Q : (gb⁻¹ * gx) * S.z * (gb⁻¹ * gx)⁻¹ ∈ S.QG := by
    rw [show (gb⁻¹ * gx) * S.z * (gb⁻¹ * gx)⁻¹ = gb⁻¹ * x * gb by rw [← hgx]; group]
    exact hxQb
  have h24b := (mem_Qa_iff S (gb⁻¹ * gx) _).mp (h24 G S hw hU _ (gb⁻¹ * gx) hy₁ hy₁M hyQb hx₁Q)
  have hx' : y * x * y⁻¹ ∈ S.Qa gx := by
    rw [mem_Qa_iff, show gx⁻¹ * (y * x * y⁻¹) * gx = (gb⁻¹ * gx)⁻¹ * ((gb⁻¹ * y * gb) *
      ((gb⁻¹ * gx) * S.z * (gb⁻¹ * gx)⁻¹) * (gb⁻¹ * y * gb)⁻¹) * (gb⁻¹ * gx) by
      rw [← hgx]; group]
    exact h24b
  have ha : (x * y) ^ 2 = x * (y * x * y⁻¹) := by rw [hyi, sq]; group
  obtain ⟨T, hT⟩ : ∃ T : Setting G, T = S.conjBy gx := ⟨_, rfl⟩
  have hTz : T.z = x := by rw [hT]; exact hgx
  have hxT : x ∈ T.QG := hTz ▸ T.z_mem_QG
  have hcQ : y * x * y⁻¹ ∈ T.QG := by rw [hT]; exact hx'
  have hcl : T.cl (y * x * y⁻¹) = T.cl (x * (y * x * y⁻¹)) := by
    rw [T.cl_mul hxT hcQ, ← hTz, T.cl_z, zero_add]
  have hne1 : x * (y * x * y⁻¹) ≠ 1 := by
    intro h1
    apply hxy2Q
    rw [ha, h1]
    exact S.QG.one_mem
  have hTc : IsConj T.z (y * x * y⁻¹) := by
    rw [hTz]
    exact isConj_iff.mpr ⟨y, rfl⟩
  have hconj := isConj_of_cl_eq T hTc hcQ (T.QG.mul_mem hxT hcQ) hne1 hcl
  rw [ha]
  exact hx.trans (hTz ▸ hconj)

end CFSG.GF2Type.SmithTypeE.E8
