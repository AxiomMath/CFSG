module

public import CFSG.GF2Type.SmithTypeE.E7.ModAct
public import CFSG.GF2Type.SmithTypeE.E7.Qa

public section

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent
  instCommGroupOfIsSimpleGroupOfIsNilpotent

namespace CFSG.GF2Type.SmithTypeE.E7

open Subgroup CFSG.Open CFSG.LargeExtraspecial CFSG.LargeExtraspecial.S14
open CFSG.SmithD6 (wt tvCols applyCols)
open CFSG.GF2Type.SmithTypeE.DMod (code32)
open CFSG.LargeExtraspecial.S14.SME (inv_eq_of_isConj mem_Qa_iff mem_Qa_symm mem_M_conj_iff
  isConj_of_cl_eq)
open scoped MatrixGroups

@[expose] def InE (k i : Nat) : Prop := ∃ c < 2 ^ 32, applyCols (tvCols k) c ^^^ c = wt i

@[expose] noncomputable def applyWord : List Nat → Nat → Nat
  | [], c => c
  | r :: w, c => applyCols (tvCols r) (applyWord w c)

structure E23FourFacts7 : Prop where
  tv_invol : ∀ {r : Nat}, r < 365211 → ∀ c < 2 ^ 32,
    applyCols (tvCols r) (applyCols (tvCols r) c) = c
  word : ∀ {k i₀ i : Nat}, k < 365211 → i₀ < 75735 → i < 75735 → InE k i₀ → InE k i →
    ∃ w : List Nat, (∀ r ∈ w, r < 365211 ∧ ∀ c < 2 ^ 32,
      applyCols (tvCols r) (applyCols (tvCols k) c) =
        applyCols (tvCols k) (applyCols (tvCols r) c)) ∧ applyWord w (wt i₀) = wt i
  plane : ∀ {k l : Nat}, k < 365211 → l < 365211 → k ≠ l →
    (¬ ∀ c < 2 ^ 32, applyCols (tvCols k) (applyCols (tvCols l) c) =
      applyCols (tvCols l) (applyCols (tvCols k) c)) →
    (¬ ∀ c < 2 ^ 32, applyCols (tvCols k) (applyCols (tvCols l) (applyCols (tvCols k) c)) =
      applyCols (tvCols l) (applyCols (tvCols k) (applyCols (tvCols l) c))) →
    ∃ i < 75735, InE k i ∧ applyCols (tvCols l) (wt i) = wt i ∧ ¬ InE l i

variable {G : Type} [Group G] [Finite G]

theorem acts_inv {S : Setting G} {φ : S.Qt ≃ₗ[ZMod 2] (Fin 32 → ZMod 2)} {g : G} {F : Nat → Nat}
    (hgM : g ∈ S.M) (hg : Acts S φ g F) (hF : ∀ c < 2 ^ 32, F (F c) = c) :
    Acts S φ g⁻¹ F := by
  intro u hu
  have hu' : g⁻¹ * u * g ∈ S.QG := by
    simpa using S.conj_mem_QG (S.M.inv_mem hgM) hu
  have h1 := hg (g⁻¹ * u * g) hu'
  rw [show g * (g⁻¹ * u * g) * g⁻¹ = u by group] at h1
  rw [h1, hF _ (psi_lt S φ _), inv_inv]

theorem acts_one_of_mem_QG {S : Setting G} {φ : S.Qt ≃ₗ[ZMod 2] (Fin 32 → ZMod 2)} {q : G}
    (hq : q ∈ S.QG) : Acts S φ q (fun c => c) := by
  intro u hu
  rw [cl_conj_of_mem_QG hq hu]

theorem acts_mul_of_mem_QG {S : Setting G} {φ : S.Qt ≃ₗ[ZMod 2] (Fin 32 → ZMod 2)} {q m : G}
    {F : Nat → Nat} (hq : q ∈ S.QG) (hmM : m ∈ S.M) (hm : Acts S φ m F) :
    Acts S φ (q * m) F := fun u hu => (acts_one_of_mem_QG (φ := φ) hq |>.mul hmM hm) u hu

theorem acts_conj_of_comm {S : Setting G} {φ : S.Qt ≃ₗ[ZMod 2] (Fin 32 → ZMod 2)} {g m : G}
    {F H : Nat → Nat} (hgM : g ∈ S.M) (hmM : m ∈ S.M) (hg : Acts S φ g F) (hm : Acts S φ m H)
    (hH : ∀ c < 2 ^ 32, H (H c) = c) (hc : ∀ c < 2 ^ 32, H (F c) = F (H c)) :
    Acts S φ (m * g * m⁻¹) F := by
  intro u hu
  have h := ((hm.mul hgM hg).mul (S.M.inv_mem hmM) (acts_inv hmM hm hH)) u hu
  rw [h]
  have hcu : code32 (φ (S.cl u)) < 2 ^ 32 := psi_lt S φ _
  show H (F (H _)) = F _
  rw [hc _ (hm.lt hcu), hH _ hcu]

theorem exists_centralizer_word (hF : E23FourFacts7) (h34b : SmithE7E34b) [IsSimpleGroup G]
    (S : Setting G) (hw : S.width = 16) (hU : Nonempty (S.Mbar ≃* timmesfeldOmegaPlus 6))
    {φ : S.Qt ≃ₗ[ZMod 2] (Fin 32 → ZMod 2)}
    (h5 : ∀ r < 365211, ∃ m ∈ S.M, Acts S φ m (applyCols (tvCols r)))
    {x : G} (hx : IsConj S.z x) (hxM : x ∈ S.M) (hxQ : x ∉ S.QG) {k : Nat}
    (hA : Acts S φ x (applyCols (tvCols k))) :
    ∀ w : List Nat, (∀ r ∈ w, r < 365211 ∧ ∀ c < 2 ^ 32,
      applyCols (tvCols r) (applyCols (tvCols k) c) =
        applyCols (tvCols k) (applyCols (tvCols r) c)) →
      ∃ m ∈ S.M, m * x = x * m ∧ Acts S φ m (applyWord w) := by
  have hAA := hA.invol hx hxM
  have hxi := inv_eq_of_isConj S hx
  intro w
  induction w with
  | nil =>
    intro _
    exact ⟨1, S.M.one_mem, by simp, fun u hu => by simp [applyWord]⟩
  | cons r w ih =>
    intro hw'
    obtain ⟨m₀, hm₀M, hm₀x, hm₀⟩ := ih (fun r' hr' => hw' r' (List.mem_cons_of_mem _ hr'))
    obtain ⟨hr, hcomm⟩ := hw' r (List.mem_cons_self ..)
    obtain ⟨m_r, hm_rM, hm_r⟩ := h5 r hr
    have hx'c : IsConj S.z (m_r * x * m_r⁻¹) := hx.trans (isConj_iff.mpr ⟨m_r, rfl⟩)
    have hx'M : m_r * x * m_r⁻¹ ∈ S.M :=
      S.M.mul_mem (S.M.mul_mem hm_rM hxM) (S.M.inv_mem hm_rM)
    have hx'A : Acts S φ (m_r * x * m_r⁻¹) (applyCols (tvCols k)) :=
      acts_conj_of_comm hxM hm_rM hA hm_r (hF.tv_invol hr) hcomm
    have hxx'Q : x⁻¹ * (m_r * x * m_r⁻¹) ∈ S.QG := by
      rw [hxi]
      exact mem_QG_of_acts (S.M.mul_mem hxM hx'M) (hA.mul hx'M hx'A) fun c hc => hAA c hc
    obtain ⟨q, hqQ, hq⟩ := h34b G S hw hU x _ hx hx'c hxM hxQ hxx'Q
    have hm'x : (q * m_r) * x = x * (q * m_r) := by
      calc (q * m_r) * x = q * (m_r * x * m_r⁻¹) * m_r := by group
        _ = q * (q⁻¹ * x * q) * m_r := by rw [hq]
        _ = x * (q * m_r) := by group
    have hm'M : q * m_r ∈ S.M := S.M.mul_mem (S.QG_le_M hqQ) hm_rM
    have hm' : Acts S φ (q * m_r) (applyCols (tvCols r)) := acts_mul_of_mem_QG hqQ hm_rM hm_r
    have hfin := hm'.mul hm₀M hm₀
    refine ⟨q * m_r * m₀, S.M.mul_mem hm'M hm₀M, ?_, fun u hu => hfin u hu⟩
    calc q * m_r * m₀ * x = q * m_r * (m₀ * x) := by group
      _ = q * m_r * (x * m₀) := by rw [hm₀x]
      _ = (q * m_r * x) * m₀ := by group
      _ = x * (q * m_r) * m₀ := by rw [hm'x]
      _ = x * (q * m_r * m₀) := by group

theorem exists_mem_Qa_of_class (hF : E23FourFacts7) (h33 : SmithE7E33) (h34a : SmithE7E34a)
    (h34b : SmithE7E34b) [IsSimpleGroup G] (S : Setting G) (hw : S.width = 16)
    (hU : Nonempty (S.Mbar ≃* timmesfeldOmegaPlus 6)) {φ : S.Qt ≃ₗ[ZMod 2] (Fin 32 → ZMod 2)}
    (h2a : ∀ c : G, IsConj S.z c → c ∈ S.QG → c ≠ S.z → ∃ i < 75735, code32 (φ (S.cl c)) = wt i)
    (h5 : ∀ r < 365211, ∃ m ∈ S.M, Acts S φ m (applyCols (tvCols r)))
    {g : G} (hxM : g * S.z * g⁻¹ ∈ S.M) (hxQ : g * S.z * g⁻¹ ∉ S.QG) {k : Nat} (hk : k < 365211)
    (hA : Acts S φ (g * S.z * g⁻¹) (applyCols (tvCols k))) {i : Nat} (hi : i < 75735)
    (hEi : InE k i) :
    ∃ b : G, IsConj S.z b ∧ b ∈ S.QG ∧ code32 (φ (S.cl b)) = wt i ∧ b ∈ S.Qa g := by
  have hx : IsConj S.z (g * S.z * g⁻¹) := isConj_iff.mpr ⟨g, rfl⟩
  obtain ⟨v, hv, hvQ, hvQa⟩ := h33 G S hw hU g hxM hxQ
  have hvz : v ≠ S.z := by
    rintro rfl
    exact SMF.conj_z_not_mem_QG S hxQ ((mem_Qa_iff S g S.z).mp hvQa)
  obtain ⟨i₀, hi₀, hvi⟩ := h2a v hv hvQ hvz
  have hcomm := mem_commQt_of_mem_Qa h34a S hw hU hxM hxQ hvQ hvQa
  obtain ⟨c, hc, hcv⟩ := code_mem_commQt hxM hA hcomm
  have hE₀ : InE k i₀ := ⟨c, hc, hcv.symm.trans hvi⟩
  obtain ⟨w, hw', hwi⟩ := hF.word hk hi₀ hi hE₀ hEi
  obtain ⟨m, hmM, hmx, hmw⟩ :=
    exists_centralizer_word hF h34b S hw hU h5 hx hxM hxQ hA w hw'
  have hm' : g⁻¹ * m * g ∈ S.M := (mem_M_conj_iff S g m).mpr hmx
  have hvg : g⁻¹ * v * g ∈ S.QG := (mem_Qa_iff S g v).mp hvQa
  refine ⟨m * v * m⁻¹, hv.trans (isConj_iff.mpr ⟨m, rfl⟩), S.conj_mem_QG hmM hvQ, ?_, ?_⟩
  · rw [hmw v hvQ, hvi, hwi]
  · rw [mem_Qa_iff, show g⁻¹ * (m * v * m⁻¹) * g =
      (g⁻¹ * m * g) * (g⁻¹ * v * g) * (g⁻¹ * m * g)⁻¹ by group]
    exact S.conj_mem_QG hm' hvg

theorem smithE7E23Four_of (hF : E23FourFacts7) (hM : SmithE7Model) (h33 : SmithE7E33)
    (h34a : SmithE7E34a) (h34b : SmithE7E34b) (h24 : SmithE7E24) : SmithE7E23Four := by
  intro G _ _ _ S hw hU x y hx hy hxM hyM hxQ hyQ hxyQ hxy2Q hxy4Q
  obtain ⟨φ, h2a, -, -, h4, h5⟩ := hM G S hw hU
  obtain ⟨k, hk, hA⟩ := h4 x hx hxM hxQ
  obtain ⟨l, hl, hB⟩ := h4 y hy hyM hyQ
  change Acts S φ x (applyCols (tvCols k)) at hA
  change Acts S φ y (applyCols (tvCols l)) at hB
  have hAA := hA.invol hx hxM
  have hBB := hB.invol hy hyM
  have hxi := inv_eq_of_isConj S hx
  have hyi := inv_eq_of_isConj S hy
  have hkl : k ≠ l := by
    rintro rfl
    exact hxyQ (mem_QG_of_acts (S.M.mul_mem hxM hyM) (hA.mul hyM hB) fun c hc => hAA c hc)
  have hncomm : ¬ ∀ c < 2 ^ 32, applyCols (tvCols k) (applyCols (tvCols l) c) =
      applyCols (tvCols l) (applyCols (tvCols k) c) :=
    fun hc => hxy2Q (sq_mem_of_comm hxM hyM hA hB hAA hBB hc)
  have hnbraid : ¬ ∀ c < 2 ^ 32,
      applyCols (tvCols k) (applyCols (tvCols l) (applyCols (tvCols k) c)) =
        applyCols (tvCols l) (applyCols (tvCols k) (applyCols (tvCols l) c)) := by
    intro hbr
    apply hxyQ
    have h3 := cube_mem_of_braid hxM hyM hA hB hAA hBB hbr
    have e : (x * y) ^ 4 = (x * y) * (x * y) ^ 3 := pow_succ' (x * y) 3
    have := S.QG.mul_mem hxy4Q (S.QG.inv_mem h3)
    rwa [e, mul_inv_cancel_right] at this
  obtain ⟨i, hi, hEki, hfix, hnEl⟩ := hF.plane hk hl hkl hncomm hnbraid
  obtain ⟨gx, hgx⟩ := isConj_iff.mp hx
  obtain ⟨gy, hgy⟩ := isConj_iff.mp hy
  obtain ⟨b, hb, hbQ, hbi, hbx⟩ := exists_mem_Qa_of_class hF h33 h34a h34b S hw hU h2a h5
    (g := gx) (hgx ▸ hxM) (hgx ▸ hxQ) hk (hgx ▸ hA) hi hEki
  have hfixy := fixQt_eq_of_smithE7E34a h34a S hw hU hy hyM hyQ
  have hby : y * b = b * y := by
    refine S.commute_of_cl_mem_fixQt hyM hfixy hbQ ?_
    rw [S.cl_mem_fixQt_iff hyM hbQ]
    apply psi_inj S φ
    rw [hB b hbQ, hbi, hfix]
  have hbQy : b ∉ S.Qa gy := by
    intro hbQa
    have hcomm := mem_commQt_of_mem_Qa h34a S hw hU (g := gy) (hgy ▸ hyM) (hgy ▸ hyQ) hbQ hbQa
    rw [hgy] at hcomm
    obtain ⟨c, hc, hcb⟩ := code_mem_commQt hyM hB hcomm
    exact hnEl ⟨c, hc, hcb.symm.trans hbi⟩
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
  set T := S.conjBy gx with hT
  have hTz : T.z = x := hgx
  have hxT : x ∈ T.QG := hTz ▸ T.z_mem_QG
  have hcQ : y * x * y⁻¹ ∈ T.QG := hx'
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

end CFSG.GF2Type.SmithTypeE.E7
