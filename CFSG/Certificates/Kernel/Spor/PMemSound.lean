module

public import Certificates.Data.Kernel.Spor.PMem
public import CFSG.Certificates.Kernel.Spor.PRecSound

public section

namespace CFSG.KS.PMem

open CFSG.KC.Enum CFSG.KS CFSG.KS.Raw CFSG.KS.Prim CFSG.KS.PEnum CFSG.KS.Raw.Orb Subgroup
  CFSG.KS.PRec

variable {n w : ℕ}

theorem atK_spec {cnt : ℕ} {T POS : ℕ → ℕ} {i Q : ℕ} (h : atK cnt T POS i Q = true) :
    r32 POS i < cnt ∧ T (r32 POS i) = Q := by
  unfold atK at h
  rw [Orb.strictB_eq, bAnd_eq, Bool.and_eq_true] at h
  exact ⟨Nat.blt_eq.mp h.1, Nat.eq_of_beq_eq_true h.2⟩

theorem listed_of_atK {cnt : ℕ} {T POS : ℕ → ℕ} {i Q : ℕ} {x : ℕ → Equiv.Perm (Fin n)}
    (hx : ∀ q < cnt, PRep n w (T q) (x q)) {g : Equiv.Perm (Fin n)} (hg : PRep n w Q g)
    (h : atK cnt T POS i Q = true) : ∃ q < cnt, x q = g := by
  obtain ⟨hlt, he⟩ := atK_spec h
  have h1 := hx _ hlt
  rw [he] at h1
  exact ⟨_, hlt, CFSG.KC.OrbGroup.prep_eq h1 hg⟩

theorem mem_of_atK {cnt : ℕ} {T POS : ℕ → ℕ} {i Q : ℕ} {x : ℕ → Equiv.Perm (Fin n)}
    {H : Subgroup (Equiv.Perm (Fin n))} (hx : ∀ q < cnt, PRep n w (T q) (x q))
    (hH : ∀ y, y ∈ H ↔ ∃ q < cnt, x q = y) {g : Equiv.Perm (Fin n)} (hg : PRep n w Q g)
    (h : atK cnt T POS i Q = true) : g ∈ H :=
  (hH g).2 (listed_of_atK hx hg h)

theorem conjInK_spec (hn : n < 2 ^ 32) {cnt : ℕ} {T POS A AI B : ℕ → ℕ} {ka kb : ℕ}
    {x a b : ℕ → Equiv.Perm (Fin n)} {H : Subgroup (Equiv.Perm (Fin n))}
    (hx : ∀ q < cnt, PRep n w (T q) (x q)) (hH : ∀ y, y ∈ H ↔ ∃ q < cnt, x q = y)
    (ha : ∀ i < ka, PRep n w (A i) (a i)) (hai : ∀ i < ka, PRep n w (AI i) (a i)⁻¹)
    (hb : ∀ j < kb, PRep n w (B j) (b j))
    (h : conjInK n w (mask w) cnt T POS A AI B ka kb = true) :
    ∀ i < ka, ∀ j < kb, a i * b j * (a i)⁻¹ ∈ H := by
  intro i hi j hj
  have h1 := allN_iff.1 (allN_iff.1 h i hi) j hj
  exact mem_of_atK hx hH (prep_pcomp hn (prep_pcomp hn (ha i hi) (hb j hj)) (hai i hi)) h1

theorem commInK_spec (hn : n < 2 ^ 32) {cnt : ℕ} {T POS A AI : ℕ → ℕ} {ka : ℕ}
    {x a : ℕ → Equiv.Perm (Fin n)} {H : Subgroup (Equiv.Perm (Fin n))}
    (hx : ∀ q < cnt, PRep n w (T q) (x q)) (hH : ∀ y, y ∈ H ↔ ∃ q < cnt, x q = y)
    (ha : ∀ i < ka, PRep n w (A i) (a i)) (hai : ∀ i < ka, PRep n w (AI i) (a i)⁻¹)
    (h : commInK n w (mask w) cnt T POS A AI ka = true) :
    ∀ i < ka, ∀ j < ka, a i * a j * (a i)⁻¹ * (a j)⁻¹ ∈ H := by
  intro i hi j hj
  have h1 := allN_iff.1 (allN_iff.1 h i hi) j hj
  exact mem_of_atK hx hH (prep_pcomp hn (prep_pcomp hn (prep_pcomp hn (ha i hi) (ha j hj))
    (hai i hi)) (hai j hj)) h1

theorem pcomp_eq_of_prep (hn : n < 2 ^ 32) (hw : 0 < w) {P Q P' Q' : ℕ} {g : Equiv.Perm (Fin n)}
    (h1 : PRep n w (pcomp n w (mask w) P Q) g) (h2 : PRep n w (pcomp n w (mask w) P' Q') g) :
    pcomp n w (mask w) P Q = pcomp n w (mask w) P' Q' :=
  CFSG.KS.PF.eq_of_fields hw (CFSG.KS.PF.pcomp_shr P Q hn hw) (CFSG.KS.PF.pcomp_shr P' Q' hn hw)
    fun i hi => by rw [h1 ⟨i, hi⟩, h2 ⟨i, hi⟩]

theorem commAllK_of_comm (hn : n < 2 ^ 32) (hw : 0 < w) {k P : ℕ} {G : ℕ → ℕ}
    {g : ℕ → Equiv.Perm (Fin n)} {s : Equiv.Perm (Fin n)} (hs : PRep n w P s)
    (hg : ∀ j < k, PRep n w (G j) (g j)) (hc : ∀ j < k, s * g j = g j * s) :
    commAllK n w (mask w) k G P = true := by
  unfold commAllK
  refine allN_iff.2 fun j hj => ?_
  have h1 := prep_pcomp hn hs (hg j hj)
  rw [hc j hj] at h1
  rw [pcomp_eq_of_prep hn hw h1 (prep_pcomp hn (hg j hj) hs)]
  exact Nat.beq_refl _

theorem centOneK_spec (hn : n < 16777216) (hw : n + 1 < 2 ^ w) {cnt k : ℕ} {T G : ℕ → ℕ}
    {x g : ℕ → Equiv.Perm (Fin n)} (hx : ∀ q < cnt, PRep n w (T q) (x q))
    (hg : ∀ j < k, PRep n w (G j) (g j))
    (h : centOneK n w (mask w) (pidn n w) cnt T k G = true) :
    ∀ q < cnt, (∀ j < k, x q * g j = g j * x q) → x q = 1 := by
  intro q hq hc
  have h1 := allN_iff.1 h q hq
  rw [commAllK_of_comm (by omega) (CFSG.KS.PF.w_pos hw) (hx q hq) hg hc] at h1
  have h2 := hx q hq
  rw [Nat.eq_of_beq_eq_true h1] at h2
  exact CFSG.KC.OrbGroup.prep_eq h2 (prep_pidn hn hw)

theorem filtInK_spec (hn : n < 2 ^ 32) (hw : 0 < w) {cnt k cnt' : ℕ} {T G T' POS : ℕ → ℕ}
    {x x' g : ℕ → Equiv.Perm (Fin n)} (hx : ∀ q < cnt, PRep n w (T q) (x q))
    (hx' : ∀ q < cnt', PRep n w (T' q) (x' q)) (hg : ∀ j < k, PRep n w (G j) (g j))
    (h : filtInK n w (mask w) cnt T k G cnt' T' POS = true) :
    ∀ q < cnt, (∀ j < k, x q * g j = g j * x q) → ∃ q' < cnt', x' q' = x q := by
  intro q hq hc
  have h1 := allN_iff.1 h q hq
  rw [commAllK_of_comm hn hw (hx q hq) hg hc] at h1
  exact listed_of_atK hx' (hx q hq) h1

theorem commToK_spec (hn : n < 2 ^ 32) {cnt cnt' Z : ℕ} {T POS T' POS' : ℕ → ℕ}
    {x x' : ℕ → Equiv.Perm (Fin n)} {z : Equiv.Perm (Fin n)}
    (hx : ∀ q < cnt, PRep n w (T q) (x q)) (hx' : ∀ q < cnt', PRep n w (T' q) (x' q))
    (hz : PRep n w Z z) (h : commToK n w (mask w) cnt T POS cnt' T' POS' Z = true) :
    ∃ p < cnt, ∃ q < cnt', x p * x' q = z * x' q * x p := by
  unfold commToK at h
  rw [Orb.strictB_eq, Orb.strictB_eq, bAnd_eq, bAnd_eq, Bool.and_eq_true, Bool.and_eq_true] at h
  obtain ⟨hp, hq, he⟩ := h
  have hp' := Nat.blt_eq.mp hp
  have hq' := Nat.blt_eq.mp hq
  have h1 := prep_pcomp hn (hx _ hp') (hx' _ hq')
  rw [Nat.eq_of_beq_eq_true he] at h1
  exact ⟨_, hp', _, hq', CFSG.KC.OrbGroup.prep_eq h1
    (prep_pcomp hn (prep_pcomp hn hz (hx' _ hq')) (hx _ hp'))⟩

theorem notCentK_spec (hn : n < 2 ^ 32) (hw : 0 < w) {cnt Z k : ℕ} {T POS G : ℕ → ℕ}
    {x g : ℕ → Equiv.Perm (Fin n)} {z : Equiv.Perm (Fin n)}
    (hx : ∀ q < cnt, PRep n w (T q) (x q)) (hz : PRep n w Z z)
    (hg : ∀ j < k, PRep n w (G j) (g j))
    (h : notCentK n w (mask w) (n * w) cnt T POS Z k G = true) :
    ∃ p < cnt, x p * z = z * x p ∧ ¬ ∀ j < k, x p * g j = g j * x p := by
  unfold notCentK at h
  rw [Orb.strictB_eq, bAnd_eq, bAnd_eq, Bool.and_eq_true, Bool.and_eq_true] at h
  obtain ⟨hp, hc, hn'⟩ := h
  have hp' := Nat.blt_eq.mp hp
  refine ⟨_, hp', ?_, fun hall => ?_⟩
  · have hk : centK n w (mask w) (n * w) 1 (fun _ => T (r32 POS 0)) Z = true :=
      allN_iff.2 fun _ _ => hc
    exact comm_of_centK hn (k := 1) (g := fun _ => x (r32 POS 0)) (fun _ _ => hx _ hp') hz hk 0
      Nat.one_pos
  · rw [commAllK_of_comm hn hw (hx _ hp') hg hall] at hn'
    exact Bool.false_ne_true hn'

end CFSG.KS.PMem

end
