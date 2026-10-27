module

public import CFSG.GH74.QTGen4.Recog.G23.P7.Leaf.Cor37B

public section

namespace CFSG.GH74.QTGen4.Recog.G23.P7.Cor37

open CFSG.GH74.QTGen4.Recog.G23 CFSG.GH74.QTGen4.Recog.G23.P7

section PartE

variable {G : Type} [Group G]

theorem mem_sup_of_cent {C N L : Subgroup G} (hN : ∀ c ∈ C, ∀ n ∈ N, c * n * c⁻¹ ∈ N)
    (hLC : L ≤ C) {g : G} (hg : g ∈ N ⊔ L) : ∃ n ∈ N, ∃ l ∈ L, n * l = g := by
  let S : Subgroup G :=
    { carrier := {x | ∃ n ∈ N, ∃ l ∈ L, n * l = x}
      one_mem' := ⟨1, N.one_mem, 1, L.one_mem, by simp⟩
      mul_mem' := by
        rintro _ _ ⟨n, hn, l, hl, rfl⟩ ⟨n', hn', l', hl', rfl⟩
        refine ⟨n * (l * n' * l⁻¹), N.mul_mem hn (hN l (hLC hl) n' hn'), l * l',
          L.mul_mem hl hl', ?_⟩
        group
      inv_mem' := by
        rintro _ ⟨n, hn, l, hl, rfl⟩
        refine ⟨l⁻¹ * n⁻¹ * l, by simpa using hN l⁻¹ (C.inv_mem (hLC hl)) n⁻¹ (N.inv_mem hn),
          l⁻¹, L.inv_mem hl, ?_⟩
        group }
  have hle : N ⊔ L ≤ S := by
    refine sup_le ?_ ?_
    · intro n hn
      exact ⟨n, hn, 1, L.one_mem, by simp⟩
    · intro l hl
      exact ⟨1, N.one_mem, l, hl, by simp⟩
  exact hle hg

theorem mem_sup_comm {A B : Subgroup G} (h : ∀ a ∈ A, ∀ b ∈ B, a * b = b * a) {g : G}
    (hg : g ∈ A ⊔ B) : ∃ a ∈ A, ∃ b ∈ B, a * b = g := by
  let S : Subgroup G :=
    { carrier := {x | ∃ a ∈ A, ∃ b ∈ B, a * b = x}
      one_mem' := ⟨1, A.one_mem, 1, B.one_mem, by simp⟩
      mul_mem' := by
        rintro _ _ ⟨a, ha, b, hb, rfl⟩ ⟨a', ha', b', hb', rfl⟩
        refine ⟨a * a', A.mul_mem ha ha', b * b', B.mul_mem hb hb', ?_⟩
        calc a * a' * (b * b') = a * (a' * b) * b' := by group
          _ = a * (b * a') * b' := by rw [h a' ha' b hb]
          _ = a * b * (a' * b') := by group
      inv_mem' := by
        rintro _ ⟨a, ha, b, hb, rfl⟩
        refine ⟨a⁻¹, A.inv_mem ha, b⁻¹, B.inv_mem hb, ?_⟩
        have hc : a * b = b * a := h a ha b hb
        have hc' : b⁻¹ * a⁻¹ = a⁻¹ * b⁻¹ := by
          have := congrArg (fun y => y⁻¹) hc
          simp only [mul_inv_rev] at this
          exact this
        rw [mul_inv_rev]
        exact hc'.symm }
  have hle : A ⊔ B ≤ S := by
    refine sup_le ?_ ?_
    · intro a ha
      exact ⟨a, ha, 1, B.one_mem, by simp⟩
    · intro b hb
      exact ⟨1, A.one_mem, b, hb, by simp⟩
  exact hle hg

theorem zpowers_involution_cases {z w : G} (hz : z * z = 1) (hw : w ∈ Subgroup.zpowers z) :
    w = 1 ∨ w = z := by
  obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.mp hw
  have hz2 : z ^ (2 : ℤ) = 1 := by
    rw [zpow_two]
    exact hz
  have hk : z ^ k = z ^ (k % 2) := by
    have hdecomp : k = 2 * (k / 2) + k % 2 := by omega
    conv_lhs => rw [hdecomp, zpow_add, zpow_mul, hz2, one_zpow, one_mul]
  rcases Int.emod_two_eq_zero_or_one k with h | h
  · left
    rw [hk, h, zpow_zero]
  · right
    rw [hk, h, zpow_one]

theorem sq_mem_of_cent {P Pb : Subgroup G} {z : G}
    (hnorm : ∀ c ∈ Subgroup.centralizer (P : Set G), ∀ n ∈ Pb, c * n * c⁻¹ ∈ Pb)
    (hsup : ∀ x ∈ Subgroup.centralizer (P : Set G), x ∈ Pb ⊔ Subgroup.zpowers z)
    (hz : z * z = 1) (hzC : z ∈ Subgroup.centralizer (P : Set G))
    {x : G} (hx : x ∈ Subgroup.centralizer (P : Set G)) : x * x ∈ Pb := by
  have hLC : Subgroup.zpowers z ≤ Subgroup.centralizer (P : Set G) :=
    Subgroup.zpowers_le.mpr hzC
  obtain ⟨p, hp, w, hw, hpw⟩ := mem_sup_of_cent hnorm hLC (hsup x hx)
  rcases zpowers_involution_cases hz hw with rfl | rfl
  · rw [← hpw]
    have : p * 1 * (p * 1) = p * p := by group
    rw [this]
    exact Pb.mul_mem hp hp
  · rw [← hpw]
    have heq : p * w * (p * w) = p * (w * p * w⁻¹) * (w * w) := by group
    rw [heq, hz, mul_one]
    exact Pb.mul_mem hp (hnorm w hzC p hp)

theorem odd_mem_of_cent {P Pb : Subgroup G} (hsq : ∀ x ∈ Subgroup.centralizer (P : Set G), x * x ∈ Pb)
    {x : G} (hx : x ∈ Subgroup.centralizer (P : Set G)) {n : ℕ} (hn : Odd n) (hxn : x ^ n = 1) :
    x ∈ Pb := by
  obtain ⟨k, rfl⟩ := hn
  have h : (x * x) ^ (k + 1) = x := by
    calc (x * x) ^ (k + 1) = x ^ (2 * (k + 1)) := by rw [← sq, ← pow_mul]
      _ = x := by
        rw [show 2 * (k + 1) = (2 * k + 1) + 1 by ring, pow_succ, hxn, one_mul]
  rw [← h]
  exact Pb.pow_mem (hsq x hx) (k + 1)

theorem mem_cent_closure {σ τ m : G} {P : Subgroup G}
    (hPgen : P = Subgroup.closure ({σ, τ} : Set G))
    (hσm : σ * m = m * σ) (hτm : τ * m = m * τ) :
    m ∈ Subgroup.centralizer (P : Set G) := by
  rw [Subgroup.mem_centralizer_iff]
  intro h hh
  rw [hPgen] at hh
  have hle : Subgroup.closure ({σ, τ} : Set G) ≤ Subgroup.centralizer {m} := by
    rw [Subgroup.closure_le]
    intro x hx
    rcases hx with rfl | rfl
    · exact Subgroup.mem_centralizer_singleton_iff.mpr hσm
    · exact Subgroup.mem_centralizer_singleton_iff.mpr hτm
  exact Subgroup.mem_centralizer_singleton_iff.mp (hle hh)

theorem pb_eq_sup {σ τ z : G} {P Pb M L : Subgroup G} (hPgen : P = Subgroup.closure {σ, τ})
    (hcc : IsCentComplement (Subgroup.centralizer (P : Set G)) (Subgroup.zpowers z) Pb)
    (hPPb : P ≤ Pb)
    (hMC : IsCentComplement (Subgroup.centralizer ({τ} : Set G)) L M)
    (hM3 : IsPGroup 3 M)
    (hσL : σ ∈ L) (hzL : z ∈ L)
    (hcentL : ∀ l ∈ L, l * σ = σ * l → l ∈ Subgroup.zpowers σ ⊔ Subgroup.zpowers z)
    (hz : z * z = 1) (hστ : σ * τ = τ * σ) (hσz : σ * z = z * σ) (hzτ : z * τ = τ * z) :
    Pb = (M ⊓ Subgroup.centralizer {σ}) ⊔ Subgroup.zpowers σ := by
  have hσP : σ ∈ P := by
    rw [hPgen]
    exact Subgroup.subset_closure (by simp)
  have hτP : τ ∈ P := by
    rw [hPgen]
    exact Subgroup.subset_closure (by simp)
  have hσPb : σ ∈ Pb := hPPb hσP
  have hzC : z ∈ Subgroup.centralizer (P : Set G) :=
    mem_cent_closure hPgen (by rw [← hσz]) hzτ.symm
  have hsq : ∀ x ∈ Subgroup.centralizer (P : Set G), x * x ∈ Pb := fun x hx =>
    sq_mem_of_cent (P := P) (Pb := Pb) (z := z) hcc.conj_mem
      (fun y hy => by rw [hcc.sup_eq]; exact hy) hz hzC hx
  have hσC : σ ∈ Subgroup.centralizer {τ} := Subgroup.mem_centralizer_singleton_iff.mpr hστ
  have hMin : ∀ m ∈ M, m * σ = σ * m → m ∈ Pb := by
    intro m hm hmσ
    have hmτ : m * τ = τ * m := Subgroup.mem_centralizer_singleton_iff.mp (hMC.left_le hm)
    have hmC : m ∈ Subgroup.centralizer (P : Set G) :=
      mem_cent_closure hPgen hmσ.symm hmτ.symm
    obtain ⟨k, hk⟩ := hM3 ⟨m, hm⟩
    have hmk : m ^ (3 ^ k) = 1 := by
      have := congrArg Subtype.val hk
      simpa using this
    exact odd_mem_of_cent hsq hmC (Odd.pow (by decide)) hmk
  apply le_antisymm
  · intro g hg
    have hgC : g ∈ Subgroup.centralizer (P : Set G) := hcc.left_le hg
    have hgσ : g * σ = σ * g := by
      have := (Subgroup.mem_centralizer_iff.mp hgC) σ (hPgen ▸ hσP)
      exact this.symm
    have hgτ : g * τ = τ * g := by
      have := (Subgroup.mem_centralizer_iff.mp hgC) τ (hPgen ▸ hτP)
      exact this.symm
    have hgsup : g ∈ M ⊔ L := by
      rw [hMC.sup_eq]
      exact Subgroup.mem_centralizer_singleton_iff.mpr hgτ
    obtain ⟨m, hm, l, hl, hml⟩ := mem_sup_of_cent hMC.conj_mem hMC.right_le hgsup
    have hlσ : l * σ = σ * l := by
      have hu : l * σ * l⁻¹ ∈ L := L.mul_mem (L.mul_mem hl hσL) (L.inv_mem hl)
      have hconjg : g * σ * g⁻¹ = σ := by
        rw [hgσ]
        group
      have hkey : m * (l * σ * l⁻¹) * m⁻¹ = σ := by
        rw [← hml] at hconjg
        calc m * (l * σ * l⁻¹) * m⁻¹ = m * l * σ * (m * l)⁻¹ := by group
          _ = σ := hconjg
      have hu_eq : l * σ * l⁻¹ = m⁻¹ * σ * m := by
        calc l * σ * l⁻¹ = m⁻¹ * (m * (l * σ * l⁻¹) * m⁻¹) * m := by group
          _ = m⁻¹ * σ * m := by rw [hkey]
      have hMu : (l * σ * l⁻¹) * σ⁻¹ ∈ M := by
        rw [hu_eq]
        have : m⁻¹ * σ * m * σ⁻¹ = m⁻¹ * (σ * m * σ⁻¹) := by group
        rw [this]
        exact M.mul_mem (M.inv_mem hm) (hMC.conj_mem σ hσC m hm)
      have hu1 : (l * σ * l⁻¹) * σ⁻¹ ∈ L := L.mul_mem hu (L.inv_mem hσL)
      have hone : (l * σ * l⁻¹) * σ⁻¹ = 1 := by
        have hmem : (l * σ * l⁻¹) * σ⁻¹ ∈ M ⊓ L := ⟨hMu, hu1⟩
        rw [hMC.disjoint, Subgroup.mem_bot] at hmem
        exact hmem
      have hconj : l * σ * l⁻¹ = σ := mul_inv_eq_one.mp hone
      calc l * σ = (l * σ * l⁻¹) * l := by group
        _ = σ * l := by rw [hconj]
    have hmσ : m * σ = σ * m := by
      have h1 : m * l * σ = σ * (m * l) := by
        rw [hml]
        exact hgσ
      have h2 : m * σ * l = σ * m * l := by
        calc m * σ * l = m * (σ * l) := by group
          _ = m * (l * σ) := by rw [hlσ]
          _ = m * l * σ := by group
          _ = σ * (m * l) := h1
          _ = σ * m * l := by group
      exact mul_right_cancel h2
    have hcomm : ∀ a ∈ Subgroup.zpowers σ, ∀ b ∈ Subgroup.zpowers z, a * b = b * a := by
      intro a ha b hb
      have hbσ : b * σ = σ * b := (mem_zpowers_commute hσz hb).symm
      exact (mem_zpowers_commute hbσ ha).symm
    obtain ⟨a, ha, b, hb, hab⟩ := mem_sup_comm hcomm (hcentL l hl hlσ)
    have haPb : a ∈ Pb := (Subgroup.zpowers_le.mpr hσPb) ha
    have hmPb : m ∈ Pb := hMin m hm hmσ
    have hb1 : b = 1 := by
      have hbPb : b ∈ Pb := by
        have hbeq : b = a⁻¹ * m⁻¹ * g := by
          rw [← hml, ← hab]
          group
        rw [hbeq]
        exact Pb.mul_mem (Pb.mul_mem (Pb.inv_mem haPb) (Pb.inv_mem hmPb)) hg
      have hmem : b ∈ Pb ⊓ Subgroup.zpowers z := ⟨hbPb, hb⟩
      rw [hcc.disjoint, Subgroup.mem_bot] at hmem
      exact hmem
    have hgeq : g = m * a := by
      rw [← hml, ← hab, hb1, mul_one]
    rw [hgeq]
    exact Subgroup.mul_mem _
      (Subgroup.mem_sup_left (show m ∈ M ⊓ Subgroup.centralizer {σ} from
        ⟨hm, Subgroup.mem_centralizer_singleton_iff.mpr hmσ⟩))
      (Subgroup.mem_sup_right ha)
  · apply sup_le
    · intro m hm
      exact hMin m hm.1 (Subgroup.mem_centralizer_singleton_iff.mp hm.2)
    · exact Subgroup.zpowers_le.mpr hσPb

theorem card_pb_eq [Finite G] {σ τ z : G} {P Pb M L : Subgroup G} (hσ3 : orderOf σ = 3)
    (hPgen : P = Subgroup.closure ({σ, τ} : Set G))
    (hcc : IsCentComplement (Subgroup.centralizer (P : Set G)) (Subgroup.zpowers z) Pb)
    (hPPb : P ≤ Pb)
    (hMC : IsCentComplement (Subgroup.centralizer ({τ} : Set G)) L M)
    (hM3 : IsPGroup 3 M)
    (hσL : σ ∈ L) (hzL : z ∈ L)
    (hcentL : ∀ l ∈ L, l * σ = σ * l → l ∈ Subgroup.zpowers σ ⊔ Subgroup.zpowers z)
    (hz : z * z = 1) (hστ : σ * τ = τ * σ) (hσz : σ * z = z * σ) (hzτ : z * τ = τ * z) :
    Nat.card ↥Pb = 3 * Nat.card ↥(M ⊓ Subgroup.centralizer {σ}) := by
  rw [pb_eq_sup hPgen hcc hPPb hMC hM3 hσL hzL hcentL hz hστ hσz hzτ]
  apply card_sup_zpowers_of_commute σ hσ3
  · intro a ha
    exact (Subgroup.mem_centralizer_singleton_iff.mp ha.2)
  · apply le_bot_iff.mp
    intro x hx
    rw [Subgroup.mem_bot]
    have hxM : x ∈ M := hx.1.1
    have hxL : x ∈ L := (Subgroup.zpowers_le.mpr hσL) hx.2
    have hmem : x ∈ M ⊓ L := ⟨hxM, hxL⟩
    rw [hMC.disjoint, Subgroup.mem_bot] at hmem
    exact hmem

end PartE

end CFSG.GH74.QTGen4.Recog.G23.P7.Cor37
