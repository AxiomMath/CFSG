module

public import CFSG.CGT.PushingUpLit.CGT6.Emb5Coinv
public import CFSG.CGT.PushingUpLit.CGT6.Emb5Four
public import CFSG.CGT.PushingUpLit.CGT6.EmbEight
public import CFSG.CGT.PushingUpLit.CGT6E.Emb55Conj

public section

namespace CFSG.CGT.PushingUpLit.CGT6

open CFSG CFSG.Quasithin

variable {V : Type} [CommGroup V] [Finite V] {G T Y : Subgroup (MulAut V)}

theorem Emb5Cfg.card_le_sixtyfour (cfg : Emb5Cfg G T Y) (hV : ∀ v : V, v ^ 2 = 1) {g t : MulAut V}
    (htY : ∀ y ∈ Y, t * y = y * t) (ht2 : t ^ 2 = 1)
    (hgen : CGT6E.conjSub g Y ⊔ Y ⊔ Subgroup.zpowers t = G) :
    Nat.card V ≤ 64 := by
  set X : Subgroup (MulAut V) := CGT6E.conjSub g Y with hX
  set Xt : Subgroup (MulAut V) := CGT6E.conjSub t X with hXt
  have hYt : ∀ y ∈ Y, t * y * t⁻¹ = y := fun y hy => by
    calc t * y * t⁻¹ = y * t * t⁻¹ := by rw [htY y hy]
      _ = y := by group
  have htinv : t⁻¹ = t := by
    have h1 : t * t = 1 := by rw [← pow_two]; exact ht2
    exact inv_eq_of_mul_eq_one_right h1
  have hYmap : Y.map (MulAut.conj t).toMonoidHom = Y := by
    ext z
    constructor
    · rintro ⟨y, hy, rfl⟩
      simpa [MulAut.conj_apply, hYt y hy] using hy
    · intro hz
      exact ⟨z, hz, by simpa [MulAut.conj_apply] using hYt z hz⟩
  have htt : t * t = 1 := by rw [← pow_two]; exact ht2
  have hXtX : Xt.map (MulAut.conj t).toMonoidHom = X := by
    ext z
    constructor
    · rintro ⟨_, ⟨x, hx, rfl⟩, rfl⟩
      have e : t * (t * x * t⁻¹) * t⁻¹ = x := by
        calc t * (t * x * t⁻¹) * t⁻¹ = (t * t) * x * (t * t)⁻¹ := by group
          _ = x := by rw [htt]; group
      show t * (t * x * t⁻¹) * t⁻¹ ∈ X
      rw [e]
      exact hx
    · intro hz
      refine ⟨t * z * t⁻¹, ⟨z, hz, rfl⟩, ?_⟩
      show t * (t * z * t⁻¹) * t⁻¹ = z
      calc t * (t * z * t⁻¹) * t⁻¹ = (t * t) * z * (t * t)⁻¹ := by group
        _ = z := by rw [htt]; group
  set S : Subgroup V := commV X ⊔ commV Xt ⊔ commV Y with hS
  have hGle : G ≤ (X ⊔ Xt ⊔ Y) ⊔ Subgroup.zpowers t := by
    rw [← hgen]
    exact sup_le (sup_le (le_sup_of_le_left (le_sup_of_le_left le_sup_left))
      (le_sup_of_le_left le_sup_right)) le_sup_right
  have hsup : S ⊔ commV (Subgroup.zpowers t) = ⊤ := by
    have h1 : commV G ≤ commV ((X ⊔ Xt ⊔ Y) ⊔ Subgroup.zpowers t) := commV_mono hGle
    have h2 := commV_sup_le (X ⊔ Xt ⊔ Y) (Subgroup.zpowers t)
    have h3 := commV_sup_le (X ⊔ Xt) Y
    have h4 := commV_sup_le X Xt
    rw [cfg.comm, top_le_iff] at h1
    refine top_le_iff.mp ?_
    rw [← h1]
    exact h2.trans (sup_le_sup_right (h3.trans (sup_le_sup_right h4 _)) _)
  have hStep : ∀ w ∈ S, t w ∈ S := by
    intro w hw
    have e1 : (commV X).map t.toMonoidHom = commV Xt := (commV_map_conj X t).symm
    have e2 : (commV Xt).map t.toMonoidHom = commV X := by
      rw [← commV_map_conj, hXtX]
    have e3 : (commV Y).map t.toMonoidHom = commV Y := by
      rw [← commV_map_conj, hYmap]
    obtain ⟨w', hw', w'', hw'', rfl⟩ := Subgroup.mem_sup.mp hw
    obtain ⟨a, ha, b, hb, rfl⟩ := Subgroup.mem_sup.mp hw'
    rw [map_mul, map_mul]
    refine Subgroup.mul_mem _ (Subgroup.mul_mem _ ?_ ?_) ?_
    · exact Subgroup.mem_sup_left (Subgroup.mem_sup_right (e1 ▸ Subgroup.mem_map_of_mem _ ha))
    · exact Subgroup.mem_sup_left (Subgroup.mem_sup_left (e2 ▸ Subgroup.mem_map_of_mem _ hb))
    · exact Subgroup.mem_sup_right (e3 ▸ Subgroup.mem_map_of_mem _ hw'')
  have hSinv : ∀ x ∈ Subgroup.zpowers t, ∀ w ∈ S, x w ∈ S := by
    intro x hx w hw
    obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.mp hx
    rcases Int.even_or_odd k with ⟨m, rfl⟩ | ⟨m, rfl⟩
    · have : t ^ (m + m) = 1 := by
        rw [← two_mul, zpow_mul]
        simp [ht2]
      rw [this]
      simpa using hw
    · have : t ^ (2 * m + 1) = t := by
        rw [zpow_add, zpow_mul]
        simp [ht2]
      rw [this]
      exact hStep w hw
  have hStop : S = ⊤ := eq_top_of_sup_commV_eq_top hV (isPGroup_zpowers_of_sq ht2) hSinv hsup
  have hY4 := cfg.adm.h4
  have hX4 : Nat.card ↥(commV X) = 4 := by
    rw [hX, CGT6E.card_commV_conjSub]
    exact hY4
  have hXt4 : Nat.card ↥(commV Xt) = 4 := by
    rw [hXt]
    exact (CGT6E.card_commV_conjSub t X).trans hX4
  have c1 := card_sup_le_mul (commV X) (commV Xt)
  have c2 := card_sup_le_mul (commV X ⊔ commV Xt) (commV Y)
  rw [hX4, hXt4] at c1
  rw [hY4] at c2
  have c3 : Nat.card V = Nat.card ↥S := by
    rw [hStop]
    exact (Nat.card_congr Subgroup.topEquiv.toEquiv).symm
  rw [c3]
  calc Nat.card ↥S ≤ Nat.card ↥(commV X ⊔ commV Xt) * 4 := c2
    _ ≤ 4 * 4 * 4 := Nat.mul_le_mul_right 4 c1
    _ = 64 := by norm_num

theorem Emb5Cfg.commV_gen (cfg : Emb5Cfg G T Y) {g t : MulAut V}
    (hgen : CGT6E.conjSub g Y ⊔ Y ⊔ Subgroup.zpowers t = G) :
    commV Y ⊔ commV (CGT6E.conjSub g Y) ⊔ commV (Subgroup.zpowers t) = ⊤ := by
  have h1 : commV G ≤ commV (CGT6E.conjSub g Y ⊔ Y) ⊔ commV (Subgroup.zpowers t) := by
    rw [← hgen]
    exact commV_sup_le _ _
  have h2 : commV (CGT6E.conjSub g Y ⊔ Y) ≤ commV (CGT6E.conjSub g Y) ⊔ commV Y :=
    commV_sup_le _ _
  rw [cfg.comm, top_le_iff] at h1
  refine top_le_iff.mp ?_
  rw [← h1]
  calc commV (CGT6E.conjSub g Y ⊔ Y) ⊔ commV (Subgroup.zpowers t)
      ≤ (commV (CGT6E.conjSub g Y) ⊔ commV Y) ⊔ commV (Subgroup.zpowers t) :=
        sup_le_sup_right h2 _
    _ = commV Y ⊔ commV (CGT6E.conjSub g Y) ⊔ commV (Subgroup.zpowers t) := by
        rw [sup_comm (commV (CGT6E.conjSub g Y))]

end CFSG.CGT.PushingUpLit.CGT6
