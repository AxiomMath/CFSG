module

public import Certificates.Certificate725001

public section

namespace CFSG.SectionRank.QTK.Insp443.M24

open CFSG.Sporadic.Th CFSG.Sporadic.Th.Native CFSG.Sporadic.Schreier CFSG.Sporadic.Schreier.Native
  CFSG.Quasithin.KGC31.Native CFSG.Quasithin.KGC31.M24 CFSG.Certificates _root_.Certificates

theorem k_g1 :
    (invOK 24 gT (invT 24 gT) && (conjAll gT tT).all (inSpan 24 etT)) = true := by
  obtain ⟨h, -⟩ := Certificates.certificate725001
  exact h

theorem k_g2 :
    (invOK 24 zT (invT 24 zT) && invOK 24 lT (invT 24 lT) &&
      lqChain.sift (tab (wordG gensG lW)) 0 && ebasisOK 24 sixT &&
      sixT.all (inSpan 24 etT)) = true := by
  obtain ⟨-, h, -⟩ := Certificates.certificate725001
  exact h

theorem k_g3 :
    (ordTest 24 7 xT && commT 24 b0T xT && cjT.all (commT 24 b0T) && cbChain.check &&
      (cbChain.orderCertificate == 21504)) = true := by
  obtain ⟨-, -, h, -⟩ := Certificates.certificate725001
  exact h

theorem k_g4 :
    (invOK 24 nT (invT 24 nT) && masksOK 24 etT nT nMasks &&
      (lqGen.all fun g => invOK 24 (toTable g) (invT 24 (toTable g)) &&
        inSpan 24 etT
          (compT 24 (conjTab 24 (toTable g) (invT 24 (toTable g)) nT) (invT 24 nT))) &&
      ebasisOK 24 (u5T ++ conjAll nT u5T) && u5T.all (inSpan 24 etT) &&
      ((nqGen.zip nqEtMasks).all fun p => masksOK 24 etT (toTable p.1) p.2) &&
      masksOK 24 etT y7T y7EtMasks &&
      ((mjT.zip mjEtMasks).all fun p => masksOK 24 etT p.1 p.2)) = true := by
  obtain ⟨-, -, -, h⟩ := Certificates.certificate725001
  exact h

theorem k_g_inv :
    invOK 24 gT (invT 24 gT) = true := by
  have h₀ := k_g1
  simp only [Bool.and_eq_true, beq_iff_eq, and_assoc] at h₀
  obtain ⟨h, -⟩ := h₀
  exact h

theorem k_g_conj :
    (conjAll gT tT).all (inSpan 24 etT) = true := by
  have h₀ := k_g1
  simp only [Bool.and_eq_true, beq_iff_eq, and_assoc] at h₀
  obtain ⟨-, h⟩ := h₀
  exact h

theorem k_z_inv :
    invOK 24 zT (invT 24 zT) = true := by
  have h₀ := k_g2
  simp only [Bool.and_eq_true, beq_iff_eq, and_assoc] at h₀
  obtain ⟨h, -⟩ := h₀
  exact h

theorem k_l_inv :
    invOK 24 lT (invT 24 lT) = true := by
  have h₀ := k_g2
  simp only [Bool.and_eq_true, beq_iff_eq, and_assoc] at h₀
  obtain ⟨-, h, -⟩ := h₀
  exact h

theorem k_l_sift :
    lqChain.sift (tab (wordG gensG lW)) 0 = true := by
  have h₀ := k_g2
  simp only [Bool.and_eq_true, beq_iff_eq, and_assoc] at h₀
  obtain ⟨-, -, h, -⟩ := h₀
  exact h

theorem k_six_eb :
    ebasisOK 24 sixT = true := by
  have h₀ := k_g2
  simp only [Bool.and_eq_true, beq_iff_eq, and_assoc] at h₀
  obtain ⟨-, -, -, h, -⟩ := h₀
  exact h

theorem k_six_span :
    sixT.all (inSpan 24 etT) = true := by
  have h₀ := k_g2
  simp only [Bool.and_eq_true, beq_iff_eq, and_assoc] at h₀
  obtain ⟨-, -, -, -, h⟩ := h₀
  exact h

theorem k_x_ord :
    ordTest 24 7 xT = true := by
  have h₀ := k_g3
  simp only [Bool.and_eq_true, beq_iff_eq, and_assoc] at h₀
  obtain ⟨h, -⟩ := h₀
  exact h

theorem k_x_comm :
    commT 24 b0T xT = true := by
  have h₀ := k_g3
  simp only [Bool.and_eq_true, beq_iff_eq, and_assoc] at h₀
  obtain ⟨-, h, -⟩ := h₀
  exact h

theorem k_cj_comm :
    cjT.all (commT 24 b0T) = true := by
  have h₀ := k_g3
  simp only [Bool.and_eq_true, beq_iff_eq, and_assoc] at h₀
  obtain ⟨-, -, h, -⟩ := h₀
  exact h

theorem k_cb_check :
    cbChain.check = true := by
  have h₀ := k_g3
  simp only [Bool.and_eq_true, beq_iff_eq, and_assoc] at h₀
  obtain ⟨-, -, -, h, -⟩ := h₀
  exact h

theorem k_cb_order :
    cbChain.orderCertificate = 21504 := by
  have h₀ := k_g3
  simp only [Bool.and_eq_true, beq_iff_eq, and_assoc] at h₀
  obtain ⟨-, -, -, -, h⟩ := h₀
  exact h

theorem k_n_inv :
    invOK 24 nT (invT 24 nT) = true := by
  have h₀ := k_g4
  simp only [Bool.and_eq_true, beq_iff_eq, and_assoc] at h₀
  obtain ⟨h, -⟩ := h₀
  exact h

theorem k_n_masks :
    masksOK 24 etT nT nMasks = true := by
  have h₀ := k_g4
  simp only [Bool.and_eq_true, beq_iff_eq, and_assoc] at h₀
  obtain ⟨-, h, -⟩ := h₀
  exact h

theorem k_n_comm :
    (lqGen.all fun g => invOK 24 (toTable g) (invT 24 (toTable g)) &&
      inSpan 24 etT
        (compT 24 (conjTab 24 (toTable g) (invT 24 (toTable g)) nT) (invT 24 nT))) = true := by
  have h₀ := k_g4
  simp only [Bool.and_eq_true, beq_iff_eq, and_assoc] at h₀
  obtain ⟨-, -, h, -⟩ := h₀
  exact h

theorem k_n_eb :
    ebasisOK 24 (u5T ++ conjAll nT u5T) = true := by
  have h₀ := k_g4
  simp only [Bool.and_eq_true, beq_iff_eq, and_assoc] at h₀
  obtain ⟨-, -, -, h, -⟩ := h₀
  exact h

theorem k_u5_span :
    u5T.all (inSpan 24 etT) = true := by
  have h₀ := k_g4
  simp only [Bool.and_eq_true, beq_iff_eq, and_assoc] at h₀
  obtain ⟨-, -, -, -, h, -⟩ := h₀
  exact h

theorem k_nq_masks :
    ((nqGen.zip nqEtMasks).all fun p => masksOK 24 etT (toTable p.1) p.2) = true := by
  have h₀ := k_g4
  simp only [Bool.and_eq_true, beq_iff_eq, and_assoc] at h₀
  obtain ⟨-, -, -, -, -, h, -⟩ := h₀
  exact h

theorem k_y7_masks :
    masksOK 24 etT y7T y7EtMasks = true := by
  have h₀ := k_g4
  simp only [Bool.and_eq_true, beq_iff_eq, and_assoc] at h₀
  obtain ⟨-, -, -, -, -, -, h, -⟩ := h₀
  exact h

theorem k_mj_masks :
    ((mjT.zip mjEtMasks).all fun p => masksOK 24 etT p.1 p.2) = true := by
  have h₀ := k_g4
  simp only [Bool.and_eq_true, beq_iff_eq, and_assoc] at h₀
  obtain ⟨-, -, -, -, -, -, -, h⟩ := h₀
  exact h

end CFSG.SectionRank.QTK.Insp443.M24

end
